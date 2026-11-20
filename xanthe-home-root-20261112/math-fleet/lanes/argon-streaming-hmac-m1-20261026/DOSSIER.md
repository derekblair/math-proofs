# DOSSIER — Streaming SHA-256 + HMAC-SHA-256: Milestone-1 Statement-Pinning Preparation

- **Date:** 2026-10-27
- **Lane:** `argon-streaming-hmac-m1-20261026` · **Harness:** `agy` (Gemini 4 Argon High) · **Machine:** `bossman-vm` · **Pool:** `google-ai-ultra`
- **Deliverable type:** Research-only statement-pinning preparation dossier (zero code, repository, or GitHub writes; prepares — and does not itself constitute — `~/workspace/math-fleet/pins/<slug>.md`)
- **Predecessor baseline:** [`SHA256-DOSSIER.md`](file:///root/math-fleet/lanes/argon-streaming-hmac-m1-20261026/SHA256-DOSSIER.md) (`argon-sha256-research-20261026`, harvested 2026-10-26)
- **Pin-manifest contract:** [`pin-manifest-template.md`](file:///root/math-fleet/files/pin-manifest-template.md) (adopted 2026-10-26)
- **Target toolchain & license bar:** `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`, published `2026-09-24T20:24:21Z`), `Init`/`Std` only (zero `Mathlib`, zero `mdgen`, zero C FFI), `Apache-2.0`, `axiom_allowlist: [propext, Classical.choice, Quot.sound]`, `native_decide` / `Lean.ofReduceBool` / `bv_decide` / custom axioms / `sorry` in closures strictly forbidden.

---

## 1. M1 Scope, Frozen

### 1.1 Verbatim Predecessor Definition of Milestone M1

In [`SHA256-DOSSIER.md`](file:///root/math-fleet/lanes/argon-streaming-hmac-m1-20261026/SHA256-DOSSIER.md) §3 (lines 277 and 297–304), the common milestone bar and Milestone `M1` are defined verbatim as follows:

> All milestones target a standalone package on the programme's pinned toolchain (`leanprover/lean4:v4.34.1`), **zero external dependencies** (`Init` / `Std` only — no `Mathlib`, no `mdgen`, no FFI), licensed `Apache-2.0`. Every milestone must leave `lake build` green with **zero `sorry`s, zero `admit`s, zero `native_decide`, zero `bv_decide`**, and pass compile-time `#guard_msgs in #print axioms` checks showing only subsets of `[propext, Classical.choice, Quot.sound]`.

> #### M1 — Clean-Room FIPS 180-4 & FIPS 198-1 Pure Functional Spec + Proved Padding (`Spec/`)
> - **Dependencies:** None (root milestone).
> - **Scope:** Author the standalone, human-readable mathematical specifications of SHA-256 (FIPS 180-4 §§3–6.2) and HMAC-SHA-256 (FIPS 198-1 / RFC 2104) over `BitVec 32`, `Vector`, `List Bool`, and `List UInt8` with `set_option autoImplicit false` and zero imperative `Id.run do` blocks. Prove the mathematical properties of FIPS §5.1.1 padding and Merkle–Damgård aligned-block splitting directly in the spec package. Perform independent second-model English back-translation fidelity check on every definition against NIST FIPS 180-4 / 198-1 text.
> - **Deliverable:**
>   - `Spec/SHA256.lean`: `Word`, `Block`, `Schedule`, `State`, `Digest`, `ch`, `maj`, `bigSigma0`, `bigSigma1`, `smallSigma0`, `smallSigma1`, `K`, `H0`, `schedule` (+ `schedule_lt_16`, `schedule_ge_16`), `round`, `compress`.
>   - `Spec/Padding.lean`: `padZeros`, `padBits`, `parseBits`, `sha256Bits`, `bytesToBits`, `sha256Bytes`; theorems `padZeros_spec` (unique minimal mod-512 solution), `padBits_length_dvd_512`, `padBits_injective` (domain separation), `digestToBytesBE_sha256Bits_eq_sha256Bytes`, and `sha256Bytes_prefix_blocks` (aligned 64-byte prefix midstate decomposition).
>   - `Spec/HMAC.lean`: `normalizeKey` (+ `normalizeKey_size : (normalizeKey K).size = 64`), `hmacSpec`, `hmacSpec_congr`.
> - **Acceptance evidence (kernel bar):** `lake build Spec` exits `0`; zero `sorry`s; `#guard_msgs in #print axioms` on `padZeros_spec`, `padBits_length_dvd_512`, `padBits_injective`, `sha256Bytes_prefix_blocks`, and `normalizeKey_size` shows $\subseteq \{\texttt{propext}, \texttt{Classical.choice}, \texttt{Quot.sound}\}$.

### 1.2 Exact Coverage vs. Exclusions of Predecessor M1

| Dimension | Covered Inside Literal Predecessor `M1` (`Spec/`) | Excluded From Literal Predecessor `M1` (Deferred to `M2`–`M6`) |
|---|---|---|
| **SHA-256 core spec** | Pure functional `BitVec 32` / `Vector` definitions of `Word`, `Block`, `Schedule`, `State`, `Digest`, `ch`, `maj`, `bigSigma0`, `bigSigma1`, `smallSigma0`, `smallSigma1`, `K`, `H0`, `schedule` (+ `schedule_lt_16`, `schedule_ge_16`), `round`, `compress` (`Spec/SHA256.lean`). | Unboxed `State32` scalar struct, shift/or `UInt32` ops, bounds-checked `beU32At`, 16-word circular ring-buffer schedule, `compressSlice` / `compressBlock64`, and ring-buffer equivalence proofs (`M3`: `Impl/Compress.lean`, `Equiv/Compress.lean`). |
| **Padding, parsing & domain separation** | Closed-form `padZeros`, `padBits`, fallback-free `parseBits`, `sha256Bits`, MSB-first `bytesToBits`, `sha256Bytes`; proved `padZeros_spec`, `padBits_length_dvd_512`, `padBits_injective`, and `digestToBytesBE_sha256Bits_eq_sha256Bytes` (`Spec/Padding.lean`). | SHA-224 / SHA-384 / SHA-512 / SHA-512-$t$ / SHA-1 specifications or implementations (out of campaign scope entirely; one-shot SHA-2 family is already proved in GPL-3.0 `remix7531/fips-180-4-lean`). |
| **Streaming & midstate mechanics** | **Spec-level only:** `sha256Bytes_prefix_blocks` proving that hashing `p ++ s` (with `64 ∣ p.length` and `p.length + s.length < 2^61`) equals folding `compress` over `p`'s 64-byte blocks from `H0` and running tail padding on `s` with total bit length `8 * (p.length + s.length)` (`Spec/Padding.lean`). | **All executable streaming state & equivalence:** `Impl.Hasher`, `init`, 3-path zero-copy `update`, `finalize` / `finalize?`, `Impl.sha256`, `Impl.combine`, `Hasher.ModelsFrom`, `sha256_streaming_correct`, `sha256_chunk_invariant` (`M4`: `Impl/Streaming.lean`, `Equiv/Streaming.lean`). |
| **HMAC-SHA-256** | **Spec-level only:** `normalizeKey` (handling both `≤ 64`B and `> 64`B keys with 64-byte zero-padding), `normalizeKey_size`, `hmacSpec`, `hmacSpec_congr` (`Spec/HMAC.lean`). | Reusable midstate `PreparedKey` (`istate`, `ostate`), streaming `HmacHasher` (`init`/`update`/`finalize`), `Impl.hmacSha256`, `hmac_streaming_correct`, `hmac_oneshot_correct` (`M5`), and game-based PRF security reductions (explicitly out of scope, predecessor §4.2 #5). |
| **Test vectors & whole-repo audit** | None inside `M1` itself (`M1` runs `lake build Spec` and `#print axioms` on 5 structural theorems only). | GMP `Nat`-word `KernelEval.sha256Nat` + `decide +kernel` NIST/RFC spec KATs (`M2`), streaming chunk-split kernel KATs + `lake exe cavp-suite` runtime Monte Carlo runner + metaprogramming `AxiomAudit.lean` (`M6`). |

### 1.3 Ambiguities and Governance Hazards a Pin Manifest Must Resolve Before Launch

Auditing predecessor `M1` against [`BRIEF.md`](file:///root/math-fleet/lanes/argon-streaming-hmac-m1-20261026/BRIEF.md) and [`pin-manifest-template.md`](file:///root/math-fleet/files/pin-manifest-template.md) exposes **seven concrete ambiguities** that must be resolved on the desk before freezing `statement_file.sha256`:

1. **Structural Scope Discrepancy (`BRIEF.md` §§2–4 vs. Predecessor §3 `M1`–`M6`):**
   Predecessor §3 splits the campaign into **six** single-lane milestones (`M1` = `Spec/` only; `M2` = `KernelEval` + Spec KATs; `M3` = Scalar `Compress`; `M4` = Streaming `Hasher` `init`/`update`/`finalize` + `ModelsFrom` + `sha256_chunk_invariant`; `M5` = Streaming `HMAC`; `M6` = Streaming KATs + `cavp-suite` + `AxiomAudit`). By contrast, `BRIEF.md` §§2–4 asks this `M1` dossier to specify `Hasher` state type, `update`/`finalize`, `chunk-invariance`, `Hasher.ModelsFrom`, optional midstate export/import soundness, and streaming CAVP test vectors — treating "Milestone 1" as the **Consolidated Phase-1 Streaming SHA-256 target (`M1 + M2 + M3 + M4`)** ahead of Phase-2 HMAC (`M5 + M6`).
   - *Resolution required in pin manifest:* Coordinator must choose either **Pin Scope A (Foundation Spec + Kernel KAT Anchor = Predecessor `M1 + M2`)** or **Pin Scope B (End-to-End Streaming SHA-256 = Predecessor `M1 + M2 + M3 + M4`)**. Section 3 below supplies exact, self-contained Lean 4 signatures and theorem statements for **both** scopes (`Part 3A` and `Part 3B`) so the coordinator can cut either manifest directly.
2. **The "Unanchored Spec" Hazard in Literal `M1` Alone (`M1` Without `M2` KATs):**
   Every theorem in literal predecessor `M1` (`schedule_lt_16`, `schedule_ge_16`, `padZeros_spec`, `padBits_length_dvd_512`, `padBits_injective`, `digestToBytesBE_sha256Bits_eq_sha256Bytes`, `sha256Bytes_prefix_blocks`, `normalizeKey_size`, `hmacSpec_congr`) is **completely independent of the concrete values of `K` (64 round constants), `H0` (8 IV words), rotation shift amounts (`2, 13, 22`, etc.), `ch`/`maj` boolean formulas, `bytesToBits` bit-within-byte MSB ordering, and `ipad`/`opad` (`0x36`/`0x5c`)**. If `Spec/` contains a 1-hex-digit typo in `K` or LSB-first byte decoding, `M1` still compiles with zero `sorry`s and standard axioms — freezing a **wrong hash specification** under `statement_file.sha256` that downstream lanes (`M2`–`M5`) are forbidden to edit (`pin-manifest-template.md` line 3).
   - *Resolution required in pin manifest:* Never freeze `Spec/` without kernel-checked known-answer anchor theorems inside the pinned target (at minimum FIPS 180-4 §B.1 `"abc"`, §B.2 56-byte, CAVP `0`B/`55`B/`56`B/`64`B, and RFC 4231 Cases 1, 2, & 6), either by merging `M1 + M2` or by validating `Spec/` definitions against NIST/RFC vectors on the desk *before* hashing `statement_file`.
3. **Missing Parameterized Tail-Padding / Midstate Spec Function in `Spec/Padding.lean`:**
   Predecessor §2.2 (line 162) describes `sha256Bytes_prefix_blocks` in prose as equating `sha256Bytes (p ++ s) h` (when `64 ∣ p.length`) to *"starting from midstate `(toBlocks p).foldl compress H0` and running tail padding on `s` with total bit-length `8 * (p.length + s.length)`"*, yet `M1`'s deliverable list (line 302) omits both `toBlocks` (`parseBytes64`) and the parameterized tail-hash spec function (`sha256BytesFromMidstate` / `padBitsWithTotalLen`) needed to write that right-hand side — and needed later by `M4` (`Hasher.ModelsFrom` finalization) and `M5` (midstate `HMAC` at `priorBytes = 64`).
   - *Resolution required in pin manifest:* Explicitly declare `parseBytes64`, `padBitsWithTotalLen`, and `sha256BytesFromMidstate` in `Spec/Padding.lean` (exact signatures drafted in §3.2 below).
4. **`Spec/HMAC.lean` Length-Bound Preconditions and Vacuity Risk in `hmacSpec_congr`:**
   Predecessor §2.2 line 165 mentions instantiating generic HMAC at a totalized `sha256SpecTotal : List UInt8 → List UInt8`, whereas line 167 states preconditions `K.length < 2^61` and `m.length + 64 < 2^61` (note the **`+ 64`** from prepending $K_0 \oplus \text{ipad}$, which means $m$ of length $2^{61} - 64 \le |m| < 2^{61}$ is valid for standalone SHA-256 but **exceeds** FIPS 180-4's $< 2^{64}$-bit input bound inside HMAC's inner hash!). Furthermore, `M1` line 303 names `hmacSpec_congr` without a type signature: over Lean's pure `List UInt8`, `K₁ = K₂ → m₁ = m₂ → hmacSpec K₁ m₁ = hmacSpec K₂ m₂` is **vacuously trivial by `rfl`/`subst`** (unlike slice-representation congruence in imperative languages).
   - *Resolution required in pin manifest:* Carry explicit length hypotheses `(hK : K.length < 2 ^ 61) (hm : 64 + m.length < 2 ^ 61)` on `Spec.hmacSpec` (or return `Option (Vector UInt8 32)`), and replace trivial equality congruence with two substantive theorems: (a) **hash-oracle extensionality** `hmacGen_congr` on the generic construction, and (b) **over-long key pre-hash equivalence** `hmacSpec_longKey_eq_hashedKey` (`64 < K.length → hmacSpec K m hK hm = hmacSpec (sha256Bytes K hK).toList m …`).
5. **Non-Existent `ByteArray.concat` Identifier on `leanprover/lean4:v4.34.1`:**
   Predecessor §2.4 (lines 234–247) writes `ByteArray.concat chunks` and `ctx.buf.data.toList`. Direct inspection of `leanprover/lean4` at tag `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`, `src/Init/Data/ByteArray/Basic.lean` and `Lemmas.lean`) confirms **`ByteArray.concat` does not exist in `Init`**, whereas `ByteArray.toList : ByteArray → List UInt8` (line 181) and `List.flatten : List (List α) → List α` (`Init/Data/List/Basic.lean` line 671) are standard `Init` definitions.
   - *Resolution required in pin manifest:* Express chunk concatenation in pinned theorem signatures either directly via `(chunks.map ByteArray.toList).flatten : List UInt8` or via an explicit pinned definition `def concatByteArrays (chunks : List ByteArray) : ByteArray := chunks.foldl ByteArray.append ByteArray.empty` in the statement file.
6. **Dead-Field Loophole in `Hasher.overflow` / `Hasher.finalize?` and Unpinned Midstate Export/Import Scope:**
   Predecessor §2.3 (lines 187, 195) puts `overflow : Bool` in `Hasher` and mentions `finalize? : Hasher → Option (Vector UInt8 32)`, but §2.4 (lines 234–244) pins theorems only about `Hasher.finalize` under `< 2^61`. Without pinning `finalize?`, an implementation that hardcodes `overflow := false` and silently wraps `totalBytes` mod $2^{64}$ passes every theorem in §2.4! Likewise, whether public midstate export/import (`exportMidstate?` / `fromMidstate`) is in scope or internal to `M5` (`PreparedKey`) is unstated.
   - *Resolution required in pin manifest:* Pin `finalize?_eq_some_iff` (characterizing both `< 2^61` `some` and `≥ 2^61` `none` regimes) plus **unconditional** chunk-invariance on `finalize?` (requiring **no** `< 2^61` hypothesis), and decide explicitly whether block-aligned midstate export/import is pinned in `Streaming` (exact theorem provided in §3.3).
7. **Incomplete `#print axioms` Gate & Self-Review Conflict in `M1` Scope:**
   Predecessor `M1` line 304 checks `#print axioms` on only 5 of `M1`'s 9 named theorems (omitting `schedule_lt_16`, `schedule_ge_16`, `digestToBytesBE_sha256Bits_eq_sha256Bytes`, and `hmacSpec_congr`), and line 299 assigns English back-translation fidelity checking to the `M1` authoring lane itself, conflicting with `pin-manifest-template.md`'s rule (line 39) that `review_route` must use a reviewer pool distinct from the author pool.
   - *Resolution required in pin manifest:* Require `#guard_msgs in #print axioms` on **every** pinned theorem, and route back-translation + fidelity audit to a cross-pool reviewer before pin sign-off and at closure.

---

## 2. Verbatim Primary-Source Quotes

All primary texts below were retrieved directly during this run and verified byte-for-byte against official publications (**zero `UNVERIFIED` quotes**):
- **NIST FIPS PUB 180-4**, *Secure Hash Standard (SHS)*, August 2015 (`https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf`, 833,315 bytes; DOI `10.6028/NIST.FIPS.180-4`).
- **NIST FIPS PUB 198-1**, *The Keyed-Hash Message Authentication Code (HMAC)*, July 2008 (`https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.198-1.pdf`, 129,454 bytes; DOI `10.6028/NIST.FIPS.198-1`).
- **IETF RFC 2104**, H. Krawczyk, M. Bellare, and R. Canetti, *HMAC: Keyed-Hashing for Message Authentication*, February 1997 (`https://www.rfc-editor.org/rfc/rfc2104.txt`, 22,297 bytes).

*(Typographic fidelity note: `NIST.FIPS.180-4.pdf` encodes mathematical glyphs via legacy Symbol-font Private Use Area codepoints — e.g. `U+F06C` for `ℓ`, `U+F0A3` for `≤`, `U+F0D9`/`U+F0DA`/`U+F0C5`/`U+F0D8` for `∧`/`∨`/`⊕`/`¬`, `U+F0BA` for `≡` — and positioned PDF super/subscripts. Below, those glyphs and super/subscripts are rendered in standard Unicode/ASCII notation with zero wording alterations.)*

### 2.1 (a) FIPS PUB 180-4 — Word Conventions, Functions, Constants, Padding, Parsing, and SHA-256 Compression

#### 1. Endianness, Blocks, and 32-Bit Word Operations — FIPS 180-4 §3.1 (pp. 7–8) & §3.2 (pp. 8–9)

> **3.1 Bit Strings and Integers** [...]
> 2. [...] Throughout this specification, the “big-endian” convention is used when expressing both 32- and 64-bit words, so that within each word, the most significant bit is stored in the left-most bit position.
> 3. An integer may be represented as a word or pair of words. A word representation of the message length, ℓ, in bits, is required for the padding techniques of Sec. 5.1.
>    An integer between 0 and 2^32 - 1 inclusive may be represented as a 32-bit word. The least significant four bits of the integer are represented by the right-most hex digit of the word representation. [...] The same holds true for an integer between 0 and 2^64 - 1 inclusive, which may be represented as a 64-bit word. [...]
> 4. [...] a) For SHA-1, SHA-224 and SHA-256, each message block has 512 bits, which are represented as a sequence of sixteen 32-bit words.

> **3.2 Operations on Words**
> The following operations are applied to w-bit words in all five secure hash algorithms. SHA-1, SHA-224 and SHA-256 operate on 32-bit words (w=32) [...]
> 1. Bitwise logical word operations: ∧, ∨, ⊕, and ¬ (see Sec. 2.2.2).
> 2. Addition modulo 2^w.
>    The operation x + y is defined as follows. The words x and y represent integers X and Y, where 0 ≤ X < 2^w and 0 ≤ Y < 2^w. For positive integers U and V, let U mod V be the remainder upon dividing U by V. Compute
>        Z = ( X + Y ) mod 2^w.
>    Then 0 ≤ Z < 2^w. Convert the integer Z to a word, z, and define z = x + y.
> 3. The right shift operation SHR^n(x), where x is a w-bit word and n is an integer with 0 ≤ n < w, is defined by
>        SHR^n(x) = x >> n. [...]
> 4. The rotate right (circular right shift) operation ROTR^n(x), where x is a w-bit word and n is an integer with 0 ≤ n < w, is defined by
>        ROTR^n(x) = (x >> n) ∨ (x << w - n).
>    Thus, ROTR^n(x) is equivalent to a circular shift (rotation) of x by n positions to the right.

#### 2. Logical Round/Schedule Functions and Constants — FIPS 180-4 §4.1.2 (p. 10) & §4.2.2 (p. 11)

> **4.1.2 SHA-224 and SHA-256 Functions**
> SHA-224 and SHA-256 both use six logical functions, where each function operates on 32-bit words, which are represented as x, y, and z. The result of each function is a new 32-bit word.
>
>     Ch(x, y, z)  = (x ∧ y) ⊕ (¬x ∧ z)                              (4.2)
>     Maj(x, y, z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)                     (4.3)
>     Σ_0^{256}(x) = ROTR^2(x)  ⊕ ROTR^13(x) ⊕ ROTR^22(x)            (4.4)
>     Σ_1^{256}(x) = ROTR^6(x)  ⊕ ROTR^11(x) ⊕ ROTR^25(x)            (4.5)
>     σ_0^{256}(x) = ROTR^7(x)  ⊕ ROTR^18(x) ⊕ SHR^3(x)              (4.6)
>     σ_1^{256}(x) = ROTR^17(x) ⊕ ROTR^19(x) ⊕ SHR^10(x)             (4.7)

> **4.2.2 SHA-224 and SHA-256 Constants**
> SHA-224 and SHA-256 use the same sequence of sixty-four constant 32-bit words, K_0^{256}, K_1^{256}, …, K_63^{256}. These words represent the first thirty-two bits of the fractional parts of the cube roots of the first sixty-four prime numbers. In hex, these constant words are (from left to right)
>
>     428a2f98 71374491 b5c0fbcf e9b5dba5 3956c25b 59f111f1 923f82a4 ab1c5ed5
>     d807aa98 12835b01 243185be 550c7dc3 72be5d74 80deb1fe 9bdc06a7 c19bf174
>     e49b69c1 efbe4786 0fc19dc6 240ca1cc 2de92c6f 4a7484aa 5cb0a9dc 76f988da
>     983e5152 a831c66d b00327c8 bf597fc7 c6e00bf3 d5a79147 06ca6351 14292967
>     27b70a85 2e1b2138 4d2c6dfc 53380d13 650a7354 766a0abb 81c2c92e 92722c85
>     a2bfe8a1 a81a664b c24b8b70 c76c51a3 d192e819 d6990624 f40e3585 106aa070
>     19a4c116 1e376c08 2748774c 34b0bcb5 391c0cb3 4ed8aa4a 5b9cca4f 682e6ff3
>     748f82ee 78a5636f 84c87814 8cc70208 90befffa a4506ceb bef9a3f7 c67178f2

#### 3. Padding, Block Parsing, and Initial Hash Value — FIPS 180-4 §5.1, §5.1.1 (p. 13), §5.2.1 (p. 14), & §5.3.3 (p. 15)

> **5.1 Padding the Message**
> The purpose of this padding is to ensure that the padded message is a multiple of 512 or 1024 bits, depending on the algorithm. Padding can be inserted before hash computation begins on a message, or at any other time during the hash computation prior to processing the block(s) that will contain the padding.
>
> **5.1.1 SHA-1, SHA-224 and SHA-256**
> Suppose that the length of the message, M, is ℓ bits. Append the bit “1” to the end of the message, followed by k zero bits, where k is the smallest, non-negative solution to the equation ℓ + 1 + k ≡ 448 mod 512. Then append the 64-bit block that is equal to the number ℓ expressed using a binary representation. [...] The length of the padded message should now be a multiple of 512 bits.

> **5.2.1 SHA-1, SHA-224 and SHA-256**
> For SHA-1, SHA-224 and SHA-256, the message and its padding are parsed into N 512-bit blocks, M^(1), M^(2),…, M^(N). Since the 512 bits of the input block may be expressed as sixteen 32-bit words, the first 32 bits of message block i are denoted M_0^(i), the next 32 bits are M_1^(i), and so on up to M_15^(i).

> **5.3.3 SHA-256**
> For SHA-256, the initial hash value, H^(0), shall consist of the following eight 32-bit words, in hex:
>
>     H_0^(0) = 6a09e667
>     H_1^(0) = bb67ae85
>     H_2^(0) = 3c6ef372
>     H_3^(0) = a54ff53a
>     H_4^(0) = 510e527f
>     H_5^(0) = 9b05688c
>     H_6^(0) = 1f83d9ab
>     H_7^(0) = 5be0cd19

#### 4. Message Schedule, Compression Loop, and Alternate Implementation Clause — FIPS 180-4 §6 (p. 18) & §§6.2–6.2.2 (pp. 21–23)

> **6. SECURE HASH ALGORITHMS** [...]
> For each of the secure hash algorithms, there may exist alternate computation methods that yield identical results; one example is the alternative SHA-1 computation described in Sec. 6.1.3 [which regards `{W_t}` as a 16-word circular queue]. Such alternate methods may be implemented in conformance to this standard.

> **6.2 SHA-256**
> SHA-256 may be used to hash a message, M, having a length of ℓ bits, where 0 ≤ ℓ < 2^64. The algorithm uses 1) a message schedule of sixty-four 32-bit words, 2) eight working variables of 32 bits each, and 3) a hash value of eight 32-bit words. The final result of SHA-256 is a 256-bit message digest.
>
> The words of the message schedule are labeled W_0, W_1,…, W_63. The eight working variables are labeled a, b, c, d, e, f, g, and h. The words of the hash value are labeled H_0^(i), H_1^(i),…, H_7^(i), which will hold the initial hash value, H^(0), replaced by each successive intermediate hash value (after each message block is processed), H^(i), and ending with the final hash value, H^(N). SHA-256 also uses two temporary words, T_1 and T_2.
>
> **6.2.1 SHA-256 Preprocessing**
> 1. Set the initial hash value, H^(0), as specified in Sec. 5.3.3.
> 2. The message is padded and parsed as specified in Section 5.
>
> **6.2.2 SHA-256 Hash Computation**
> The SHA-256 hash computation uses functions and constants previously defined in Sec. 4.1.2 and Sec. 4.2.2, respectively. Addition (+) is performed modulo 2^32.
>
> Each message block, M^(1), M^(2), …, M^(N), is processed in order, using the following steps:
>
>     For i=1 to N:
>     {
>        1. Prepare the message schedule, {W_t}:
>              W_t = M_t^(i)                                                    0 ≤ t ≤ 15
>              W_t = σ_1^{256}(W_{t-2}) + W_{t-7} + σ_0^{256}(W_{t-15}) + W_{t-16}  16 ≤ t ≤ 63
>
>        2. Initialize the eight working variables, a, b, c, d, e, f, g, and h, with the (i-1)st hash value:
>              a = H_0^(i-1)
>              b = H_1^(i-1)
>              c = H_2^(i-1)
>              d = H_3^(i-1)
>              e = H_4^(i-1)
>              f = H_5^(i-1)
>              g = H_6^(i-1)
>              h = H_7^(i-1)
>
>        3. For t=0 to 63:
>           {
>              T_1 = h + Σ_1^{256}(e) + Ch(e, f, g) + K_t^{256} + W_t
>              T_2 = Σ_0^{256}(a) + Maj(a, b, c)
>              h = g
>              g = f
>              f = e
>              e = d + T_1
>              d = c
>              c = b
>              b = a
>              a = T_1 + T_2
>           }
>        4. Compute the ith intermediate hash value H^(i):
>              H_0^(i) = a + H_0^(i-1)
>              H_1^(i) = b + H_1^(i-1)
>              H_2^(i) = c + H_2^(i-1)
>              H_3^(i) = d + H_3^(i-1)
>              H_4^(i) = e + H_4^(i-1)
>              H_5^(i) = f + H_5^(i-1)
>              H_6^(i) = g + H_6^(i-1)
>              H_7^(i) = h + H_7^(i-1)
>     }
>
> After repeating steps one through four a total of N times (i.e., after processing M^(N)), the resulting 256-bit message digest of the message, M, is
>
>     H_0^(N) H_1^(N) H_2^(N) H_3^(N) H_4^(N) H_5^(N) H_6^(N) H_7^(N)

---

### 2.2 (b) FIPS PUB 198-1 & RFC 2104 — HMAC Construction & Midstate Initialization

#### 1. Parameters, Length Bound, and Step-by-Step Construction — FIPS 198-1 §2.3 (p. 3) & §4 Table 1 (p. 4)

> **2.3 HMAC Parameters and Symbols**
> HMAC uses the following parameters:
> - `B`: Block size (in bytes) of the input to the Approved hash function.
> - `H`: An Approved hash function.
> - `ipad`: Inner pad; the byte x‘36’ repeated B times.
> - `K`: Secret key shared between the originator and the intended receiver(s).
> - `K_0`: The key K after any necessary pre-processing to form a B byte key.
> - `L`: Block size (in bytes) of the output of the Approved hash function.
> - `opad`: Outer pad; the byte x‘5c’ repeated B times.
> - `text`: The data on which the HMAC is calculated; text does not include the padded key. The length of text is n bits, where 0 ≤ n < 2^B - 8B.

> **4. HMAC SPECIFICATION**
> To compute a MAC over the data ‘text’ using the HMAC function, the following operation is performed:
>
>     MAC(text) = HMAC(K, text) = H((K_0 ⊕ opad) || H((K_0 ⊕ ipad) || text))
>
> **Table 1: The HMAC Algorithm**
> - **Step 1:** If the length of K = B: set K_0 = K. Go to step 4.
> - **Step 2:** If the length of K > B: hash K to obtain an L byte string, then append (B-L) zeros to create a B-byte string K_0 (i.e., K_0 = H(K) || 00...00). Go to step 4.
> - **Step 3:** If the length of K < B: append zeros to the end of K to create a B-byte string K_0 (e.g., if K is 20 bytes in length and B = 64, then K will be appended with 44 zero bytes x’00’).
> - **Step 4:** Exclusive-Or K_0 with ipad to produce a B-byte string: K_0 ⊕ ipad.
> - **Step 5:** Append the stream of data 'text' to the string resulting from step 4: (K_0 ⊕ ipad) || text.
> - **Step 6:** Apply H to the stream generated in step 5: H((K_0 ⊕ ipad) || text).
> - **Step 7:** Exclusive-Or K_0 with opad: K_0 ⊕ opad.
> - **Step 8:** Append the result from step 6 to step 7: (K_0 ⊕ opad) || H((K_0 ⊕ ipad) || text).
> - **Step 9:** Apply H to the result from step 8: H((K_0 ⊕ opad) || H((K_0 ⊕ ipad) || text)).

#### 2. Key-Midstate Precomputation Clause — FIPS 198-1 §6 (p. 6) & RFC 2104 §§2, 4 (pp. 3–4)

> **FIPS 198-1, Section 6 (IMPLEMENTATION NOTE):**
> Conceptually, the intermediate results of the compression function on the B-byte blocks (K_0 ⊕ ipad) and (K_0 ⊕ opad) can be precomputed once, at the time of generation of the key K, or before its first use. These intermediate results can be stored and then used to initialize H each time that a message needs to be authenticated using the same key. For each authenticated message using the key K, this method saves the application of the hash function of H on two B-byte blocks (i.e., on (K ⊕ ipad) and (K ⊕ opad)). This saving may be significant when authenticating short streams of data. These stored intermediate values shall be treated and protected in the same manner as secret keys.
> Choosing to implement HMAC in this manner has no effect on interoperability.

> **RFC 2104, Section 2 (Definition of HMAC, p. 3):**
> The authentication key K can be of any length up to B, the block length of the hash function. Applications that use keys longer than B bytes will first hash the key using H and then use the resultant L byte string as the actual key to HMAC. [...]
>     ipad = the byte 0x36 repeated B times
>     opad = the byte 0x5C repeated B times.
> To compute HMAC over the data `text' we perform
>     H(K XOR opad, H(K XOR ipad, text))
> Namely,
>  (1) append zeros to the end of K to create a B byte string (e.g., if K is of length 20 bytes and B=64, then K will be appended with 44 zero bytes 0x00)
>  (2) XOR (bitwise exclusive-OR) the B byte string computed in step (1) with ipad
>  (3) append the stream of data 'text' to the B byte string resulting from step (2)
>  (4) apply H to the stream generated in step (3)
>  (5) XOR (bitwise exclusive-OR) the B byte string computed in step (1) with opad
>  (6) append the H result from step (4) to the B byte string resulting from step (5)
>  (7) apply H to the stream generated in step (6) and output the result

> **RFC 2104, Section 4 (Implementation Note, p. 4):**
> The idea is that the intermediate results of the compression function on the B-byte blocks (K XOR ipad) and (K XOR opad) can be precomputed only once at the time of generation of the key K, or before its first use. These intermediate results are stored and then used to initialize the IV of H each time that a message needs to be authenticated. This method saves, for each authenticated message, the application of the compression function of H on two B-byte blocks (i.e., on (K XOR ipad) and (K XOR opad)).

#### 3. Design Consequences for M1's Spec Layer and `Hasher.ModelsFrom`

Four concrete structural requirements flow directly from these primary-source clauses into `M1` (`Spec/`) and `M4` (`Impl.Hasher` / `Hasher.ModelsFrom`):

1. **Exact `64 + m.length < 2^61` inner-hash domain bound:** For SHA-256 ($B = 64$ bytes, $8B = 512$ bits), FIPS 198-1 §2.3's bound $0 \le n < 2^{64} - 8B = 2^{64} - 512$ bits on byte-aligned `text` ($n = 8 \cdot m.\text{length}$) translates identically to **`64 + m.length < 2 ^ 61`**, because Step 5 prepends the 64-byte block $(K_0 \oplus \text{ipad})$ before applying FIPS 180-4 §5.1.1 padding (whose 64-bit length field encodes total bits $8 \cdot (64 + m.\text{length}) < 2^{64}$). Meanwhile Step 2 hashes $K$ only when $K.\text{length} > 64$, requiring `K.length < 2 ^ 61`, and Step 8's outer input $(K_0 \oplus \text{opad}) \parallel \text{innerDigest}$ has fixed length $64 + 32 = 96 < 2^{61}$ bytes.
2. **Mandatory 64-byte output invariant on `normalizeKey` across all three key-length trichotomy branches:** FIPS 198-1 Table 1 Steps 1–3 (`= 64`, `> 64`, `< 64`) must **all** produce a 64-byte `K_0` before Step 4/7 XOR — in particular, Step 2 (`K.length > 64`) hashes `K` to $L = 32$ bytes and **appends $B - L = 32$ zero bytes** (`H(K) || 0x00^32`). Pinning `(normalizeKey K hK).size = 64` rules out the exact over-long key bug found in `SentinelOps-CI/lean-toolchain` (predecessor §1.3).
3. **Why `M1` needs `sha256BytesFromMidstate` + `sha256Bytes_prefix_blocks`:** FIPS 198-1 §6 / RFC 2104 §4 specify that compressing the single 64-byte block $P_0 = K_0 \oplus \text{ipad}$ from $H^{(0)}$ yields an 8-word intermediate hash value $H^{(1)} = \text{compress}(H^{(0)}, P_0)$, and streaming `text` from IV $H^{(1)}$ with initial byte count `priorBytes = 64` produces $H((K_0 \oplus \text{ipad}) \parallel \text{text})$ **because** FIPS 180-4 §5.1.1 padding depends on the prefix $P_0$ *only* through its byte length (`64`) added into the terminal 64-bit bit-length field $\ell = 8 \cdot (64 + |\text{text}|)$. Proving `sha256Bytes_prefix_blocks` in `M1` captures this Merkle–Damgård prefix-splitting identity once at the spec level for any `64 ∣ p.length`.
4. **Why `Hasher.ModelsFrom` must be parameterized by `(iv : Spec.State) (p : Nat)`:** Seeding `Hasher` at `(state := istate, buf := .empty, totalBytes := 64, overflow := false)` satisfies `Hasher.ModelsFrom (Spec.compress Spec.H0 ipadBlock) 1 ctx []` at initialization (`p = 1` block $= 64$ prior bytes). Preserving `ModelsFrom iv p` across arbitrary `Hasher.update` calls and finalizing at bit-length `8 * (p * 64 + absorbed.length)` simultaneously proves:
   - **Streaming SHA-256 (`p = 0, iv = Spec.H0`)**,
   - **Public 64-byte-aligned midstate export/import (`p = priorBlocks`)**, and
   - **Zero-copy streaming HMAC-SHA-256 (`p = 1, iv = istate` for inner stream; `p = 1, iv = ostate` on the 32-byte inner digest for outer finalization)** without re-proving any buffer or ring-schedule lemma.

---

## 3. Proposed Exact Theorem Statements (Pin-Manifest Grade)

To resolve Ambiguity #1 (§1.3) cleanly without forcing a second research pass, the statements below are partitioned into two composable pin layers on `leanprover/lean4:v4.34.1` (`Init`/`Std` only, `set_option autoImplicit false` in every file):
- **Part 3A (`Sha256.Spec.*` — Literal Predecessor `M1`):** Pure mathematical specifications of SHA-256 and HMAC-SHA-256 plus proved padding, domain-separation, and 64-byte-aligned midstate prefix-decomposition theorems (`Spec/SHA256.lean`, `Spec/Padding.lean`, `Spec/HMAC.lean`).
- **Part 3B (`Sha256.Impl.*` & `Sha256.Equiv.*` — Stateful Streaming `Hasher`, Chunk-Invariance & Midstate Export/Import; Predecessor `M4` / Consolidated Phase-1 Streaming `M1`):** Executable streaming state machine (`init` / `update` / `finalize` / `finalize?`), prefix-parameterized simulation invariant `Hasher.ModelsFrom`, chunk-split invariance, and midstate export/import soundness.

Every Lean identifier below (`BitVec`, `Vector`, `ByteArray.toList`, `List.flatten`, `Fin.foldl`, `Vector.zipWith`, `GetElem (Vector α n) Nat`) was verified directly against `leanprover/lean4` tag `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`).

---

### 3.1 Pinned Core Types and Functional Signatures (`Spec/` & `Impl/`)

#### A. Specification Types & Entry Points (`namespace Sha256.Spec`)

```lean
set_option autoImplicit false

namespace Sha256.Spec

abbrev Word     : Type := BitVec 32
abbrev Block    : Type := Vector Word 16
abbrev Schedule : Type := Vector Word 64
abbrev State    : Type := Vector Word 8
abbrev Digest   : Type := BitVec 256

-- Spec/SHA256.lean (§4.1.2, §4.2.2, §5.3.3, §6.2.2)
def ch (x y z : Word) : Word := (x &&& y) ^^^ (~~~x &&& z)
def maj (x y z : Word) : Word := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
def bigSigma0 (x : Word) : Word := x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22
def bigSigma1 (x : Word) : Word := x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25
def smallSigma0 (x : Word) : Word := x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ (x >>> 3)
def smallSigma1 (x : Word) : Word := x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ (x >>> 10)
def K  : Schedule := #v[ ... ] -- 64 literal hex BitVec 32 words from FIPS 180-4 §4.2.2
def H0 : State    := #v[ ... ] -- 8 literal hex BitVec 32 words from FIPS 180-4 §5.3.3
def schedule (M : Block) : Schedule
def round (W : Schedule) (s : State) (t : Fin 64) : State
def compress (H : State) (M : Block) : State :=
  Vector.zipWith (· + ·) H (Fin.foldl 64 (round (schedule M)) H)

-- Spec/Padding.lean (§5.1.1, §5.2.1, §6.2)
def padZeros (ℓ : Nat) : Nat := (448 + 512 - (ℓ + 1) % 512) % 512
def bitVecToBitsBE (w : Nat) (v : BitVec w) : List Bool :=
  (List.range w).reverse.map (fun i => v.getLsbD i)
def padBitsWithTotalLen (M : List Bool) (totalBits : Nat) : List Bool :=
  M ++ [true] ++ List.replicate (padZeros M.length) false ++
    bitVecToBitsBE 64 (BitVec.ofNat 64 totalBits)
abbrev padBits (M : List Bool) : List Bool := padBitsWithTotalLen M M.length
def parseBits (P : List Bool) (h : 512 ∣ P.length) : List Block
def sha256Bits (M : List Bool) (h : M.length < 2 ^ 64) : Digest
def bytesToBits (m : List UInt8) : List Bool
def digestToBytesBE (d : Digest) : Vector UInt8 32
def sha256Bytes (m : List UInt8) (h : m.length < 2 ^ 61) : Vector UInt8 32
def parseBytes64 (p : List UInt8) (h : 64 ∣ p.length) : List Block
def sha256BytesFromMidstate (iv : State) (priorBytes : Nat) (hAligned : 64 ∣ priorBytes)
    (s : List UInt8) (hBound : priorBytes + s.length < 2 ^ 61) : Vector UInt8 32

-- Spec/HMAC.lean (FIPS 198-1 §4 Table 1)
def normalizeKeyBytes (K : List UInt8) (hK : K.length < 2 ^ 61) : List UInt8 :=
  if K.length = 64 then K
  else if hLong : 64 < K.length then (sha256Bytes K hK).toList ++ List.replicate 32 0x00
  else K ++ List.replicate (64 - K.length) 0x00
def xorPad64 (k0 : List UInt8) (padByte : UInt8) : List UInt8 :=
  k0.map (fun b => b ^^^ padByte)
def hmacSpec (K m : List UInt8) (hK : K.length < 2 ^ 61) (hm : 64 + m.length < 2 ^ 61) :
    Vector UInt8 32

end Sha256.Spec
```

#### B. Executable Streaming State & API Signatures (`namespace Sha256.Impl`)

- **State representation in words:**
  - `State32`: Unboxed 8-field product of machine `UInt32` registers (`h0` through `h7`), lifted to `Spec.State` via `toSpecState (s : State32) : Spec.State := #v[s.h0.toBitVec, …, s.h7.toBitVec]`.
  - `Hasher`: Pure functional incremental SHA-256 context carrying `(state : State32)` (the intermediate hash value $H^{(i)}$ of all full 64-byte blocks compressed so far), `(buf : ByteArray)` with proof field `(h_buf : buf.size < 64)` (the `< 64`-byte residual tail awaiting completion or padding), `(totalBytes : UInt64)` (cumulative bytes absorbed when `< 2^61`), and `(overflow : Bool)` (latches `true` iff cumulative absorbed bytes ever reach `≥ 2^61`, i.e. `≥ 2^64` bits).
  - `Midstate`: Block-aligned exportable checkpoint carrying `(state : State32)` and `(blocks : UInt64)` (count of already-compressed 64-byte blocks, valid iff `blocks.toNat < 2 ^ 55`, i.e. `blocks * 64 < 2 ^ 61` bytes).
  - `streamBytes (chunks : List ByteArray) : List UInt8 := (chunks.map ByteArray.toList).flatten` and `concatByteArrays (chunks : List ByteArray) : ByteArray := chunks.foldl ByteArray.append ByteArray.empty`.

```lean
namespace Sha256.Impl

structure State32 where
  h0 : UInt32
  h1 : UInt32
  h2 : UInt32
  h3 : UInt32
  h4 : UInt32
  h5 : UInt32
  h6 : UInt32
  h7 : UInt32
  deriving DecidableEq, Repr

structure Hasher where
  state      : State32
  buf        : ByteArray
  h_buf      : buf.size < 64
  totalBytes : UInt64
  overflow   : Bool

structure Midstate where
  state  : State32
  blocks : UInt64
  deriving DecidableEq, Repr

def Hasher.init : Hasher
def Hasher.update (ctx : Hasher) (chunk : ByteArray) : Hasher
def Hasher.finalize (ctx : Hasher) : Vector UInt8 32
def Hasher.finalize? (ctx : Hasher) : Option (Vector UInt8 32)
def Hasher.exportMidstate? (ctx : Hasher) : Option Midstate
def Hasher.fromMidstate? (ms : Midstate) : Option Hasher

def sha256 (data : ByteArray) : Vector UInt8 32 := (Hasher.init.update data).finalize
def combine (left right : ByteArray) : Vector UInt8 32 :=
  ((Hasher.init.update left).update right).finalize

abbrev streamBytes (chunks : List ByteArray) : List UInt8 :=
  (chunks.map ByteArray.toList).flatten

def concatByteArrays (chunks : List ByteArray) : ByteArray :=
  chunks.foldl ByteArray.append ByteArray.empty

end Sha256.Impl
```

---

### 3.2 Part 3A — Pinned Specification & Padding Theorems (Literal Predecessor `M1`)

#### Theorem A1–A2: Message Schedule Recurrence (`Sha256.Spec.schedule_lt_16`, `Sha256.Spec.schedule_ge_16`)

```lean
theorem Sha256.Spec.schedule_lt_16 (M : Block) (t : Nat) (ht : t < 16) :
    (schedule M)[t] = M[t]

theorem Sha256.Spec.schedule_ge_16 (M : Block) (t : Nat) (ht16 : 16 ≤ t) (ht64 : t < 64) :
    (schedule M)[t] =
      smallSigma1 (schedule M)[t - 2] + (schedule M)[t - 7] +
        smallSigma0 (schedule M)[t - 15] + (schedule M)[t - 16]
```
- **Signature in words:** For any 16-word message block `M`, words `0..15` of the 64-word schedule equal `M[t]`, and words `16..63` satisfy the exact FIPS 180-4 §6.2.2 Step 1 4-term modular recurrence.
- **Strongest published form to match/exceed:** Matches `FIPS180_4` in Isabelle/HOL AFP `Crypto_Standards` and `SHS.SHA256.schedule` in `remix7531/fips-180-4-lean` (`spec/HashAlgorithms.lean:225`), while exceeding `fips-180-4-lean` by exposing direct equational characterizations without `Id.run` `forIn`/`MProd` loop-desugaring obligations.
- **Vacuous / weakened forms to reject:** (i) Proving recurrence only for concrete `t` via `decide` without universal quantification; (ii) using `getD · 0` instead of bounds-checked `Vector` indexing `(schedule M)[t]`, which hides off-by-one index underflow when `t - 16` wraps or goes out of range.

#### Theorem A3: Padding Zero-Count Minimality (`Sha256.Spec.padZeros_spec`)

```lean
theorem Sha256.Spec.padZeros_spec (ℓ : Nat) :
    padZeros ℓ < 512 ∧
      (ℓ + 1 + padZeros ℓ) % 512 = 448 ∧
      ∀ k : Nat, k < padZeros ℓ → (ℓ + 1 + k) % 512 ≠ 448
```
- **Signature in words:** For every non-negative bit length `ℓ` (including `0`, `447`, `448`, `511`), `padZeros ℓ` lies in `[0, 512)`, solves `ℓ + 1 + k ≡ 448 (mod 512)`, and is strictly smaller than any other non-negative solution.
- **Strongest published form to match/exceed:** Matches `Nat.find_spec` / `Nat.find_min` in `remix7531/fips-180-4-lean` (`spec/Preprocessing.lean:45–52`), while removing the `Mathlib.Data.Nat.Find` dependency completely (`Init`-only `omega` proof).
- **Vacuous / weakened forms to reject:** Proving only `(ℓ + 1 + padZeros ℓ) % 512 = 448` **without** `padZeros ℓ < 512` and `∀ k < padZeros ℓ, … ≠ 448` (e.g. `padZeros ℓ + 512` also satisfies the congruence mod 512, adding a spurious extra all-zero block and breaking FIPS 180-4 conformance).

#### Theorem A4–A5: Exact Block Divisibility, Padding Injectivity, and Suffix-Freeness (`Sha256.Spec.padBits_length_dvd_512`, `Sha256.Spec.padBits_injective`, `Sha256.Spec.padBits_suffix_free`)

```lean
theorem Sha256.Spec.padBitsWithTotalLen_length_dvd_512 (M : List Bool) (totalBits : Nat) :
    512 ∣ (padBitsWithTotalLen M totalBits).length ∧
      0 < (padBitsWithTotalLen M totalBits).length

theorem Sha256.Spec.padBits_injective {M₁ M₂ : List Bool} :
    padBits M₁ = padBits M₂ → M₁ = M₂

theorem Sha256.Spec.padBits_suffix_free {M₁ M₂ P : List Bool}
    (h₁ : M₁.length < 2 ^ 64) (h₂ : M₂.length < 2 ^ 64) :
    padBits M₂ = P ++ padBits M₁ → M₁ = M₂ ∧ P = []
```
- **Signature in words:** Every padded message has positive bit length divisible by `512` (justifying total, fallback-free block parsing); `padBits` is globally injective on all bit lists (`10*` delimiter reversal); and on valid FIPS messages (`< 2^64` bits), no padded message can appear as a suffix of another distinct padded message (Merkle–Damgård length-strengthening domain separation).
- **Strongest published form to match/exceed:** Exceeds `remix7531/fips-180-4-lean` (which proves divisibility `pad_length_mod` in `spec/Preprocessing.lean` but proves neither injectivity nor suffix-freeness) and matches/generalizes Beringer et al. USENIX Security 2015 (`PrincetonUniversity/VST`, `sha/sha_padding_lemmas.v` & `HMAC_spec_pad.v`, which proves byte-aligned padding injectivity for `< 2^64`-bit messages) to **arbitrary bit-level** messages.
- **Vacuous / weakened forms to reject:** (i) Restricting `padBits_injective` to equal-length inputs `M₁.length = M₂.length → padBits M₁ = padBits M₂ → M₁ = M₂` (which collapses to trivial `List.append_cancel_right` and never tests the `10*` + 64-bit length encoding!); (ii) restricting `P` in `padBits_suffix_free` to `P = []` (collapsing suffix-freeness back to plain injectivity); (iii) parsing blocks with `List.getD · false` instead of consuming the `512 ∣ length` witness.

#### Theorem A6–A7: Bit-vs-Byte Bijection and Aligned-Prefix Midstate Decomposition (`Sha256.Spec.digestToBytesBE_sha256Bits_eq_sha256Bytes`, `Sha256.Spec.sha256Bytes_prefix_blocks`)

```lean
theorem Sha256.Spec.bytesToBits_length (m : List UInt8) :
    (bytesToBits m).length = 8 * m.length

theorem Sha256.Spec.digestToBytesBE_sha256Bits_eq_sha256Bytes
    (m : List UInt8) (h : m.length < 2 ^ 61) :
    digestToBytesBE (sha256Bits (bytesToBits m) (by rw [bytesToBits_length]; omega)) =
      sha256Bytes m h

theorem Sha256.Spec.sha256BytesFromMidstate_prefix_blocks
    (iv : State) (priorBytes : Nat) (hPrior : 64 ∣ priorBytes)
    (p s : List UInt8) (hAligned : 64 ∣ p.length)
    (hBound : priorBytes + p.length + s.length < 2 ^ 61) :
    sha256BytesFromMidstate iv priorBytes hPrior (p ++ s) (by omega) =
      sha256BytesFromMidstate
        ((parseBytes64 p hAligned).foldl compress iv)
        (priorBytes + p.length)
        (Nat.dvd_add hPrior hAligned)
        s
        (by omega)

theorem Sha256.Spec.sha256Bytes_prefix_blocks
    (p s : List UInt8) (hAligned : 64 ∣ p.length) (hBound : p.length + s.length < 2 ^ 61) :
    sha256Bytes (p ++ s) (by rw [List.length_append]; exact hBound) =
      sha256BytesFromMidstate
        ((parseBytes64 p hAligned).foldl compress H0)
        p.length
        hAligned
        s
        hBound
```
- **Signature in words:** Byte-level `sha256Bytes` agrees identically with bit-level FIPS 180-4 `sha256Bits` composed with MSB-first `bytesToBits` and big-endian digest serialization; and whenever a prefix `p` has byte length divisible by `64` (including `p = []` and multi-block `p`), hashing `p ++ s` equals folding `compress` across `p`'s 64-byte blocks into an intermediate state and running tail padding/compression on `s` using cumulative bit-length `8 * (priorBytes + p.length + s.length)`.
- **Strongest published form to match/exceed:** Matches HACL\*'s `Spec.Hash.Lemmas.update_multi_associative` + `Spec.Hash.Incremental.hash_is_hash_incremental` (`hacl-star/specs/lemmas/Spec.Hash.Incremental.fsti:22–28`) and VST's `hash_blocks` split lemmas (`PrincetonUniversity/VST`, `sha/functional_prog.v`), while explicitly exposing the arbitrary-`(iv, priorBytes)` midstate form (`sha256BytesFromMidstate_prefix_blocks`) required by FIPS 198-1 §6 / RFC 2104 §4.
- **Vacuous / weakened forms to reject:** (i) Defining `sha256Bytes` *as* `digestToBytesBE (sha256Bits (bytesToBits m) …)` without an independent byte-level `padBytes` characterization (making `digestToBytesBE_sha256Bits_eq_sha256Bytes` a `rfl` tautology unless byte-padding equivalence is also proved); (ii) omitting `priorBytes` from the terminal 64-bit length field in `sha256BytesFromMidstate` (which breaks `sha256Bytes_prefix_blocks` for every non-empty `p`!).

#### Theorem A8–A10: FIPS 198-1 Key Normalization, Long-Key Equivalence & Midstate Characterization (`Sha256.Spec.normalizeKeyBytes_length`, `Sha256.Spec.hmacSpec_longKey_eq`, `Sha256.Spec.hmacSpec_eq_midstate`)

```lean
theorem Sha256.Spec.normalizeKeyBytes_length (K : List UInt8) (hK : K.length < 2 ^ 61) :
    (normalizeKeyBytes K hK).length = 64

theorem Sha256.Spec.hmacSpec_longKey_eq (K m : List UInt8)
    (hLong : 64 < K.length) (hK : K.length < 2 ^ 61) (hm : 64 + m.length < 2 ^ 61) :
    hmacSpec K m hK hm =
      hmacSpec (sha256Bytes K hK).toList m (by simp) hm

theorem Sha256.Spec.hmacSpec_eq_midstate (K m : List UInt8)
    (hK : K.length < 2 ^ 61) (hm : 64 + m.length < 2 ^ 61) :
    let k0 := normalizeKeyBytes K hK
    let ipadBlk := parseBytes64 (xorPad64 k0 0x36) (by simp [xorPad64, normalizeKeyBytes_length])
    let opadBlk := parseBytes64 (xorPad64 k0 0x5c) (by simp [xorPad64, normalizeKeyBytes_length])
    let inner := sha256BytesFromMidstate (ipadBlk.foldl compress H0) 64 (Nat.dvd_refl 64) m hm
    hmacSpec K m hK hm =
      sha256BytesFromMidstate (opadBlk.foldl compress H0) 64 (Nat.dvd_refl 64) inner.toList (by simp)
```
*(Plus generic hash-oracle extensionality `hmacGen_congr`: if `∀ x, x.length < 2^61 → H₁ x = H₂ x`, then `hmacGen 64 32 H₁ K m = hmacGen 64 32 H₂ K m`.)*
- **Signature in words:** Across all three FIPS 198-1 Table 1 key-size branches (`= 64`, `> 64`, `< 64`), `normalizeKeyBytes` produces an exact 64-byte block; hashing an over-long key (`> 64`B) before invoking `hmacSpec` yields the identical MAC (RFC 2104 §3); and `hmacSpec` equals two 1-block midstate evaluations (`priorBytes = 64`) of `sha256BytesFromMidstate` per FIPS 198-1 §6.
- **Strongest published form to match/exceed:** Matches `Spec.HMAC.Incremental.hmac_is_hmac_incremental` (`hacl-star/specs/lemmas/Spec.HMAC.Incremental.fsti:65–68`), Isabelle AFP `FIPS198_1.thy`, and VST `HMAC256_equivalence.v` (`Equivalence`, lines 272–285 — note VST's `Equivalence` restricts `kv` to already-normalized 64-byte `Bvector b` keys in `HmacCore`, whereas our `hmacSpec` + `normalizeKeyBytes_length` + `hmacSpec_longKey_eq` covers **all** key lengths `0 ≤ K.length < 2^61`, exceeding VST's `HmacCore` core lemma on key-length generality).
- **Vacuous / weakened forms to reject:** (i) Defining `normalizeKey` via `Vector.ofFn (fun i => K.getD i 0)` so `.size = 64` holds by `rfl` from the return type `Vector UInt8 64` even if the `> 64` branch is wrong or missing; (ii) writing `hmacSpec_congr` as `K₁ = K₂ → m₁ = m₂ → hmacSpec K₁ m₁ … = hmacSpec K₂ m₂ …` (provable in one word by `subst` with zero mathematical content); (iii) omitting the `32` trailing `0x00` bytes in the `64 < K.length` branch (`SentinelOps-CI` bug, caught by both `normalizeKeyBytes_length` and RFC 4231 Cases 6–7).

---

### 3.3 Part 3B — Pinned Streaming State-Machine, Chunk-Invariance & Midstate Theorems (Predecessor `M4` / Consolidated Streaming `M1`)

#### Simulation Invariant (`Sha256.Equiv.Hasher.ModelsFrom`)

```lean
namespace Sha256.Equiv

open Sha256.Spec Sha256.Impl

structure Hasher.ModelsFrom (iv : Spec.State) (p : Nat)
    (ctx : Impl.Hasher) (absorbed : List UInt8) : Prop where
  no_overflow : ctx.overflow = false
  len_bound   : p * 64 + absorbed.length < 2 ^ 61
  total_eq    : ctx.totalBytes.toNat = p * 64 + absorbed.length
  buf_eq      : ctx.buf.toList = absorbed.drop ((absorbed.length / 64) * 64)
  state_eq    : toSpecState ctx.state =
                  (Spec.parseBytes64
                    (absorbed.take ((absorbed.length / 64) * 64))
                    (by simp [Nat.dvd_mul_left])).foldl Spec.compress iv
```
- **Invariant preservation lemmas (`init_modelsFrom`, `update_modelsFrom`, `foldl_update_modelsFrom`):**
  - `Hasher.init_modelsFrom : Hasher.ModelsFrom Spec.H0 0 Hasher.init []`
  - `Hasher.update_modelsFrom : Hasher.ModelsFrom iv p ctx m → p * 64 + m.length + chunk.size < 2 ^ 61 → Hasher.ModelsFrom iv p (ctx.update chunk) (m ++ chunk.toList)`
  - `Hasher.foldl_update_modelsFrom : Hasher.ModelsFrom iv p ctx m → p * 64 + m.length + (streamBytes chunks).length < 2 ^ 61 → Hasher.ModelsFrom iv p (chunks.foldl Hasher.update ctx) (m ++ streamBytes chunks)`

#### Theorem B1–B2: End-to-End Streaming SHA-256 Equivalence & Overflow Completeness (`Sha256.Equiv.sha256_streaming_correct`, `Sha256.Equiv.sha256_streaming_finalize?_eq`)

```lean
theorem Sha256.Equiv.sha256_streaming_correct (chunks : List ByteArray)
    (h : (Impl.streamBytes chunks).length < 2 ^ 61) :
    (chunks.foldl Impl.Hasher.update Impl.Hasher.init).finalize =
      Spec.sha256Bytes (Impl.streamBytes chunks) h

theorem Sha256.Equiv.sha256_streaming_finalize?_eq (chunks : List ByteArray) :
    (chunks.foldl Impl.Hasher.update Impl.Hasher.init).finalize? =
      if h : (Impl.streamBytes chunks).length < 2 ^ 61 then
        some (Spec.sha256Bytes (Impl.streamBytes chunks) h)
      else
        none
```
- **Signature in words:** Folding `Hasher.update` from `Hasher.init` across **any** finite list of `ByteArray` chunks (including `chunks = []`, empty `ByteArray.empty` chunks interspersed anywhere, 1-byte drips, exact 64-byte multiples, `55`B/`56`B padding-spill boundaries, and multi-block slices) and calling `finalize` produces the exact one-shot FIPS 180-4 `Spec.sha256Bytes` digest of the concatenated byte stream whenever total bytes `< 2^61`; and `finalize?` returns `some digest` below `2^61` bytes and `none` at or above `2^61` bytes without silent wraparound.
- **Strongest published form to match/exceed:**
  - *In Lean 4:* Strictly exceeds `SHS.Equiv.SHA256.sha256_correct` in `remix7531/fips-180-4-lean` (`equiv/SHA256/Main.lean:59`, which covers one-shot `ByteArray` only and lacks any streaming state machine).
  - *Across all proof assistants:* Matches Appel's VST `SHA256_Init_spec` + `SHA256_Update_spec` + `SHA256_Final_spec` (`PrincetonUniversity/VST`, `sha/spec_sha.v:142–184`, TOPLAS 2015) and HACL\*/EverCrypt's `Hacl.Streaming.Functor.update` + `digest` (`hacl-star/code/streaming/Hacl.Streaming.Functor.fsti` + `Spec.Hash.Incremental.hash_is_hash_incremental`) at the pure functional algorithm level, and **exceeds** typical `< 2^61`-preconditioned specs via `sha256_streaming_finalize?_eq`'s exact `Option` characterization of the `≥ 2^61` overflow regime.
  - *One-sentence delta vs. VST / HACL\*:* Operates on pure Lean `ByteArray` / `State32` values verified by Lean's type-theory kernel rather than C pointers / Low\* stack-heap frames compiled via CompCert or KaRaMeL.
- **Vacuous / weakened forms to reject:**
  1. **Accumulating all bytes in `Hasher` (`buf : ByteArray` growing unboundedly, running one-shot `sha256` inside `finalize`):** Satisfies `sha256_streaming_correct` trivially in $O(|M|)$ memory instead of $O(1)$! **Pin defense:** `Hasher`'s pinned structure definition (`h_buf : buf.size < 64` + 8-word `State32` + `UInt64` + `Bool`) makes unbounded buffering **type-impossible** (`buf` can hold at most 63 bytes!).
  2. **Block-aligned chunk restriction (`∀ c ∈ chunks, 64 ∣ c.size` or `c.size > 0`):** Eliminates the partial-block buffer stitch (Path 1 & Path 3) and empty-chunk edge cases — **must be rejected**.
  3. **Omitting `sha256_streaming_finalize?_eq`:** Would allow `overflow : Bool` to be hardcoded to `false` while `totalBytes` silently wraps modulo $2^{64}$ on inputs $\ge 2^{61}$ bytes.
  4. **Weakening output equality to length equality (`.size = 32`) or `BEq` without `LawfulBEq`:** Must be propositional equality `=` on `Vector UInt8 32`.

#### Theorem B3–B4: Arbitrary Chunk-Split Invariance (`Sha256.Equiv.sha256_chunk_invariant`, `Sha256.Equiv.sha256_chunk_invariant_unconditional`)

```lean
theorem Sha256.Equiv.sha256_chunk_invariant (c₁ c₂ : List ByteArray)
    (hEq : Impl.streamBytes c₁ = Impl.streamBytes c₂)
    (hLt : (Impl.streamBytes c₁).length < 2 ^ 61) :
    (c₁.foldl Impl.Hasher.update Impl.Hasher.init).finalize =
      (c₂.foldl Impl.Hasher.update Impl.Hasher.init).finalize

theorem Sha256.Equiv.sha256_chunk_invariant_unconditional (c₁ c₂ : List ByteArray)
    (hEq : Impl.streamBytes c₁ = Impl.streamBytes c₂) :
    (c₁.foldl Impl.Hasher.update Impl.Hasher.init).finalize? =
      (c₂.foldl Impl.Hasher.update Impl.Hasher.init).finalize?
```
*(Together with one-shot & zero-copy binary corollaries:)*
```lean
theorem Sha256.Equiv.sha256_oneshot_correct (data : ByteArray) (h : data.size < 2 ^ 61) :
    Impl.sha256 data = Spec.sha256Bytes data.toList (by simpa [ByteArray.size_toList] using h)

theorem Sha256.Equiv.combine_eq_oneshot_append (left right : ByteArray)
    (h : left.size + right.size < 2 ^ 61) :
    Impl.combine left right = Impl.sha256 (left ++ right)
```
- **Signature in words:** Any two chunk partitions `c₁, c₂` whose concatenated byte lists agree produce identical `finalize` digests under `< 2^61` bytes, and identical `finalize?` results (`some` or `none`) **unconditionally for all lengths**; in particular, `Impl.sha256 data` matches `Spec.sha256Bytes` on one-shot `ByteArray`s, and `Impl.combine left right` computes `Impl.sha256 (left ++ right)` without allocating `left ++ right`.
- **Strongest published form to match/exceed:** Exceeds `LeanSha256.combine` (`etheorem/LeanSha256`, which allocates `l ++ r` and has no spec proof) and `remix7531/fips-180-4-lean` (`sha256_correct`, one-shot only); matches HACL\*/EverCrypt's `seen`-ghost-state framing across arbitrary `update` sequences while adding unconditional overflow-preserving chunk invariance (`sha256_chunk_invariant_unconditional`).
- **Vacuous / weakened forms to reject:**
  1. **Hypothesizing `c₁ = c₂` instead of `Impl.streamBytes c₁ = Impl.streamBytes c₂`:** Makes chunk-invariance `rfl`!
  2. **Proving `sha256_chunk_invariant` *alone* without `sha256_streaming_correct`:** A constant function `finalize _ := Vector.replicate 32 0` is 100% chunk-invariant! Chunk-invariance is meaningful **only** alongside `sha256_streaming_correct`.
  3. **Defining `Impl.combine l r := Impl.sha256 (l ++ r)`:** Defeats zero-copy streaming; `Impl.combine` must remain definitionally `((Hasher.init.update left).update right).finalize` in the pinned statement file.

#### Theorem B5–B6: Block-Aligned Midstate Export/Import Soundness (`Sha256.Equiv.exportMidstate?_fromMidstate?_resume`, `Sha256.Equiv.fromMidstate?_streaming_correct`)

```lean
theorem Sha256.Equiv.exportMidstate?_fromMidstate?_resume
    (prefixChunks suffixChunks : List ByteArray)
    (hAligned : 64 ∣ (Impl.streamBytes prefixChunks).length)
    (hBound : (Impl.streamBytes prefixChunks).length +
                (Impl.streamBytes suffixChunks).length < 2 ^ 61) :
    ∃ ms ctx₀,
      (prefixChunks.foldl Impl.Hasher.update Impl.Hasher.init).exportMidstate? = some ms ∧
      Impl.Hasher.fromMidstate? ms = some ctx₀ ∧
      (suffixChunks.foldl Impl.Hasher.update ctx₀).finalize =
        Spec.sha256Bytes
          (Impl.streamBytes prefixChunks ++ Impl.streamBytes suffixChunks)
          (by rw [List.length_append]; exact hBound)

theorem Sha256.Equiv.fromMidstate?_streaming_correct
    (ms : Impl.Midstate) (suffixChunks : List ByteArray)
    (hBound : ms.blocks.toNat * 64 + (Impl.streamBytes suffixChunks).length < 2 ^ 61) :
    ∃ ctx₀,
      Impl.Hasher.fromMidstate? ms = some ctx₀ ∧
      (suffixChunks.foldl Impl.Hasher.update ctx₀).finalize =
        Spec.sha256BytesFromMidstate
          (toSpecState ms.state)
          (ms.blocks.toNat * 64)
          (Nat.dvd_mul_left 64 ms.blocks.toNat)
          (Impl.streamBytes suffixChunks)
          hBound
```
- **Signature in words:**
  - `exportMidstate?_fromMidstate?_resume`: After absorbing any 64-byte-aligned prefix stream (under total length `< 2^61`), `exportMidstate?` succeeds (`some ms`), `fromMidstate? ms` reconstructs a valid `Hasher` `ctx₀`, and streaming any suffix chunks into `ctx₀` yields the exact FIPS 180-4 SHA-256 digest of `prefix ++ suffix` (covering checkpoint/resume, Bitcoin/mining 64-byte header midstates, and shared-prefix hashing).
  - `fromMidstate?_streaming_correct`: Importing **any** `(state, blocks)` midstate with `blocks * 64 + |suffix| < 2^61` computes `Spec.sha256BytesFromMidstate` from `(toSpecState ms.state, ms.blocks * 64)` — directly discharging `M5`'s HMAC `istate`/`ostate` (`blocks = 1`) without opening `Hasher` internals.
- **Strongest published form to match/exceed:** Exceeds both `remix7531/fips-180-4-lean` and `PrincetonUniversity/VST` `sha/spec_sha.v` (neither exposes a verified first-class midstate export/import API, though VST uses an internal `HMAC_SHA256` midstate step and HACL\* uses internal `Spec.HMAC.Incremental` `init`).
- **Vacuous / weakened forms to reject:** (i) Using `∀ ms ctx₀, exportMidstate? … = some ms → …` **without** proving existence `∃ ms ctx₀, exportMidstate? … = some ms ∧ …` (if `exportMidstate?` always returned `none`, universal implication `exportMidstate? … = some ms → …` would hold **vacuously by `False.elim`**!); (ii) omitting the `ms.blocks.toNat < 2 ^ 55` guard in `fromMidstate?`, which would let `ms.blocks * 64` wrap around `UInt64` (`2^64`) and forge bit-lengths.

---

## 4. Test-Vector and Evidence Plan

### 4.1 Authoritative Vector Sources (One-Shot, Bit-Level, HMAC, and Streaming/Chunked)

All official vector archives below were fetched directly from NIST CSRC and IETF during this run and hashed with `sha256sum`:

| Suite / Standard | Official URL & Verified Archive `sha256` | Exact Contents & Role in Verification |
|---|---|---|
| **NIST CAVP Byte-Oriented SHA-256** (`CAVS 11.0 / 11.1`) | `https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/shs/shabytetestvectors.zip`<br>`sha256: 929ef80b7b3418aca026643f6f248815913b60e01741a44bba9e118067f4c9b8` | • `SHA256ShortMsg.rsp` (10,299 B): **65 byte-aligned vectors** (`Len = 0, 8, …, 512` bits = `0..64` bytes), hitting every mod-64 padding residue (`0`B empty, `55`B max 1-block, `56`B min 2-block spill, `63`B, `64`B full block + pad block).<br>• `SHA256LongMsg.rsp` (426,209 B): **64 multi-block vectors** (`520..129,024` bits = `65..16,128` bytes).<br>• `SHA256Monte.rsp` (8,751 B) & `SHA256Monte.txt` (149,551 B): **100 checkpoints × 1,000 inner steps** (`100,000` digests). |
| **NIST CAVP Bit-Oriented SHA-256** (`CAVS 11.0`) | `https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/shs/shabittestvectors.zip`<br>`sha256: cd7b9f11680c6e0ccdbe13b28403f2017b5ff48789152162461e0a24fb4c5d45` | • `SHA256ShortMsg.rsp` (80,540 B): non-byte-aligned bit strings (`0..512` bits in 1-bit increments) directly exercising `Spec.sha256Bits` (`List Bool`) on sub-byte padding residues (`ℓ mod 8 ≠ 0`). |
| **FIPS 180-4 Appendix B / NIST Worked Examples** | `https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/shs/sha256-384-512.pdf` & FIPS 180-4 §5.1.1 | Canonical human-readable anchor vectors: `""` (`e3b0c442…7852b855`), `"abc"` (`ba7816bf…ad015ad`), 56-byte `"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"` (`248d6a61…f20015ad`), and 112-byte `"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"` (`cf5b16a7…5f5d5a8d` / `e3b0…` family). |
| **IETF RFC 4231 Official HMAC-SHA-256 Vectors** | `https://www.rfc-editor.org/rfc/rfc4231.txt` (§4.1–§4.8, 17,725 B) | **All 7 normative test cases (Cases 1–7)**, specifically including **Case 6** (`131`-byte key `0xaa^131`, `54`-byte data: tests Step 2 key hashing + 32-byte zero-padding) and **Case 7** (`131`-byte key `0xaa^131`, `152`-byte multi-block data). |
| **NIST CAVP Official HMAC Vectors** (`CAVS 11.0`) | `https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/mac/hmactestvectors.zip`<br>`sha256: 418c3837d38f249d6668146bd0090db24dd3c02d2e6797e3de33860a387ae4bd` | • `HMAC.rsp` (849,996 B), section `[L=32]`: **225 official HMAC-SHA-256 vectors** spanning **`Klen ∈ {40, 45, 64, 70, 74}` bytes** (exercising `< 64`B, `= 64`B, and `> 64`B key normalization branches), `128`-byte messages, and `Tlen ∈ {16, 24, 32}` (`75` full 32-byte MACs + `150` truncated MACs per FIPS 198-1 §5). |
| **Streaming / Chunked & Large-Data Sources (SHAVS Monte + NIST ACVP `LDT` + Boundary Splits)** | • `SHA256Monte.txt` (`shabytetestvectors.zip`)<br>• NIST ACVP SHA JSON Spec §6.3 (`https://pages.nist.gov/ACVP/draft-celi-acvp-sha.html`, `testType: "LDT"`, Vassilev et al. ePrint `2019/1421` / CVE-2019-8741) | 1. **SHAVS Monte Carlo 3-chunk stream:** Every inner step $i \in [3, 1002]$ defines $M_i = MD_{i-3} \parallel MD_{i-2} \parallel MD_{i-1}$ (`32 + 32 + 32 = 96` bytes), fed natively as **three separate 32-byte `Hasher.update` calls** (`Path 1` buffer $\to$ `Path 3` exact 64B stitch $\to$ `Path 1` 32B tail + 1-block finalize).<br>2. **Adversarial boundary chunk splits** on FIPS §B, `SHA256ShortMsg` (`0, 3, 55, 56, 63, 64`B), `SHA256LongMsg` (`65, 128, 1024`B), and RFC 4231 Cases 1–7: `[]`, `[empty, M, empty]`, 1-byte drips (`M.toList.map singleton`), `[55, 1]`, `[56, 8]`, `[63, 1]`, `[63, 2, 63]`, `[64, 0, 64]`, and prime-step slices (`7, 13, 61, 67`B).<br>3. **NIST ACVP Large Data Test (`LDT`):** Repeated-chunk streaming past $2^{29}$ bytes ($2^{32}$ bits = 512 MiB) and $2^{32}$ bytes (4 GiB) in the compiled runner, catching 32-bit length-counter bugs (CVE-2019-8741) empirically alongside `sha256_streaming_correct`'s formal proof up to $2^{61}-1$ bytes. |

---

### 4.2 Kernel-Checked Vector Strategy Without `native_decide` or `Lean.ofReduceBool`

#### 1. Why `native_decide` and `bv_decide` Are Strictly Forbidden — and How `decide +kernel` Works on `v4.34.1`

Inspection of `src/Init/Tactics.lean` (lines 1384–1394) in `leanprover/lean4:v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) confirms:
- `native_decide` (`decide +native`) compiles Lean code to native C/LLVM and admits the Boolean result via the compiler-trust axiom `Lean.ofReduceBool` (plus `Lean.trustCompiler`), violating `trust_policy.native_decide: forbidden` and `trust_policy.ofReduceBool: forbidden` in [`pin-manifest-template.md`](file:///root/math-fleet/files/pin-manifest-template.md). Likewise, `bv_decide` verifies LRAT certificates via `native_decide`, silently injecting `Lean.ofReduceBool`.
- By contrast, **`decide +kernel`** synthesizes `Decidable p` and delegates reduction **exclusively once to Lean's C++ trusted kernel** (`ofDecideEqTrue (Eq.refl true)`), bypassing slow double-reduction in the elaborator while adding **zero axioms** (`#print axioms` on a pure `decide +kernel` equality reports *`does not depend on any axioms`*).

#### 2. Recommended Architecture: Proved GMP `Nat`-Word Bridge (`KernelEval`) + Two-Tier Execution

We endorse — and refine for both `M1`-only and consolidated `M1` scopes — predecessor §2.5's **`decide +kernel` over a GMP `Nat`-word evaluator** over all alternatives:

- **Why direct `decide +kernel` on `ByteArray` / `Vector (BitVec 32)` does not scale past ~5–10 blocks:** Inside the C++ kernel, `ByteArray` is not flat memory (`ByteArray.mk (Array.mk (List UInt8))`), and `Vector` / `Fin` indexing drags `omega` proof terms through WHNF. Conversely, Lean's C++ kernel accelerates `Nat` `+`, `&&&`, `|||`, `^^^`, `<<<`, and `>>>` natively through GMP. As verified in `keithadler/lean-x509` (`X509/Sha256.lean` + `test/Axioms.lean`), an ~80-line proof-term-free `Nat` SHA-256 evaluator (`KernelEval.sha256Nat : List Nat → List Nat`) reduces ~190+ block compressions inside `by decide +kernel` in seconds with strictly standard axioms.
- **How vectors become genuine kernel-checked theorems on `Spec` and `Impl.Hasher`:**
  1. **If `M1` is pinned as `Spec/`-only (Scope A):** Include at minimum **8 small direct `decide +kernel` anchor theorems** directly on `Spec` (`""`, `"abc"`, 56B FIPS §B.2, `55`B/`56`B/`64`B CAVP, non-byte-aligned 5-bit CAVP on `sha256Bits`, and RFC 4231 Cases 1 & 6 on `hmacSpec`) — for 1–3 block inputs on `List UInt8` / `BitVec 32` without `ByteArray`, direct `decide +kernel` finishes in `< 2` seconds even *before* `M2` builds `KernelEval`, **eliminating Ambiguity #2 (the Unanchored Spec hazard)**!
  2. **With `KernelEval` (`M2` / Consolidated Scope B):** Prove `theorem Spec.sha256Bytes_eq_sha256Nat (m : List UInt8) (h : m.length < 2 ^ 61)` once under standard axioms. Then every KAT theorem on `Spec.sha256Bytes`, `Impl.Hasher` (via `rw [Equiv.sha256_streaming_correct, Spec.sha256Bytes_eq_sha256Nat]`), and `Spec.hmacSpec` (via `KernelEval.hmacNat`) closes by `decide +kernel` in milliseconds — covering **all 65 `SHA256ShortMsg.rsp` vectors (`0..64`B)**, **FIPS §B vectors**, **selected multi-block `SHA256LongMsg.rsp` vectors (`≤ 1,024`B)**, **all 7 RFC 4231 HMAC cases**, **15 representative NIST `HMAC.rsp` `[L=32]` vectors (`Klen ∈ {40, 45, 64, 70, 74}`)**, and **20 adversarial chunk-split streaming theorems** inside `.olean` kernel checking with **zero `Lean.ofReduceBool`**.
  3. **Runtime `IO` Runner (`lake exe cavp-suite`, never imported into proof `.olean`s):** Parses unmodified NIST `SHA256ShortMsg.rsp`, `SHA256LongMsg.rsp` (up to 16 KiB), `SHA256Monte.rsp` (100,000 3-chunk streaming compressions), `HMAC.rsp` (all 225 `[L=32]` vectors), and an ACVP `LDT` multi-hundred-MiB / GiB streaming counter test, exiting `0` iff 100% pass.

---

### 4.3 Mandatory Recorded-Output Evidence Bundle for the Future M1 Proof Lane

Per [`pin-manifest-template.md`](file:///root/math-fleet/files/pin-manifest-template.md) line 45 (*"recorded outputs, never bare commands"*), a future `M1` proof lane closure artifact (`EVIDENCE.md` / closure report) must record verbatim stdout/stderr and exit codes for **five mandatory gates**:

1. **Toolchain & Zero-Dependency Pin Check:**
   - Command: `cat lean-toolchain && lean --version && lake --version && cat lake-manifest.json`
   - Required recorded output: `leanprover/lean4:v4.34.1`, `Lean (version 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, ...)`, and `"packages": []` in `lake-manifest.json` (plus `grep -i mathlib lakefile.*` returning non-zero / empty).
2. **Frozen Statement-File Hash & Immutability Check:**
   - Command: `sha256sum <repo-relative-statement-file.lean> && git status --short && git rev-parse HEAD`
   - Required recorded output: Exact 64-hex SHA-256 digest matching `statement_file.sha256` in `~/workspace/math-fleet/pins/<slug>.md` with zero modifications to any pinned signature or definition.
3. **Clean Kernel Build Command, Exit Status & Unabridged Log:**
   - Command: `lake clean && lake build; echo "BUILD_EXIT=$?"` (with `leanOptions := #[⟨`warningAsError, true⟩, ⟨`autoImplicit, false⟩]` in `lakefile.lean`).
   - Required recorded output: Complete module compilation transcript ending in `BUILD_EXIT=0` with zero warnings.
4. **Per-Theorem `#print axioms` Output + Whole-Namespace Axiom & Source Hygiene Audit:**
   - Command: `lake env lean AxiomAudit.lean; echo "AXIOM_EXIT=$?"`
   - Required recorded output:
     - Explicit `#print axioms` lines for **every theorem listed in the pin manifest's `theorems:` block** (all Part 3A theorems A1–A10, plus all Part 3B theorems B1–B6 if Scope B, plus anchor KAT theorems), each printing **only** a subset of `[propext, Classical.choice, Quot.sound]` (or `does not depend on any axioms`), guarded by `#guard_msgs`;
     - Output of an `#eval` `collectAxioms` traversal over every non-internal constant in namespace `Sha256` confirming `0` occurrences of `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, or any user axiom, ending in `AXIOM_EXIT=0`;
     - Output of `grep -rnE '\b(sorry|admit|native_decide|bv_decide|axiom|extern|implemented_by|unsafe)\b' Sha256/` confirming **0 prohibited tokens** in implementation/proof sources.
5. **Deliverable Artifact Hash Manifest:**
   - Command: `find Sha256 Tests lakefile.lean lean-toolchain LICENSE -type f | LC_ALL=C sort | xargs sha256sum && git rev-parse HEAD`
   - Required recorded output: Complete SHA-256 manifest of all repository files at the closing commit SHA.

---

## 5. Risks, Overlaps, and Open Questions

### 5.1 Dedicated Sweep for Missed Streaming SHA-256 & HMAC Repositories in Lean 4 (Critical New Findings)

To test predecessor §1.1's claim that *"no verified incremental/streaming `init`/`update`/`finalize` SHA-256 state machine exists anywhere in Lean"* and that all existing two-level SHA-256 specs in Lean 4 are `GPL-3.0-or-later` + `Mathlib`, we ran an independent sweep on 2026-10-27 across GitHub repository search (`sha256 language:Lean`, `"sha-256" language:Lean`, `hmac language:Lean`), Reservoir (`reservoir.lean-lang.org`), Brave Search (`"lean 4" "sha256" ("streaming" OR "update" OR "finalize" OR "hmac")`), `cryspen/libcrux`, `LorenaLabs/*`, and `remix7531/*`.

**Result: We uncovered THREE major permissive-licensed Lean 4 repositories (`pure-algebra/lean4-hash`, `kim-em/lean-crypto-hash`, and `pyca/verified-garbage`) — plus four minor repositories — that the predecessor dossier missed completely.** Primary-source audit of their trees, `.lean` files, licenses, axioms, and CI logs materially changes the overlap calculus for `M1`–`M6`:

| Newly Found Repository | Primary Sources Inspected (2026-10-27) | License, Deps & Toolchain | What It Already Proves | Exact Gaps Leaving Specific Space Open |
|---|---|---|---|---|
| **1. `pure-algebra/lean4-hash`**<br>**[MAJOR OVERLAP ON STREAMING SHA-256]** | [Repo](https://github.com/pure-algebra/lean4-hash) (`HEAD` `ab7eda43`, pushed `2026-10-11`), `README.md`, `Hash/Sha256/{Spec,Impl,Fast,Bridge,Context,Api,Verified}.lean`, [green CI run `38143123695`](https://github.com/pure-algebra/lean4-hash/actions/runs/38143123695) | **`MIT`** · **Zero deps** · `leanprover/lean4:v4.33.1` | **Three-level SHA-256, SHA-224 & SHA3-512 + proved streaming `Context`:** bit-level FIPS 180-4 `Spec.sha256_bytes` ↔ byte-level `Impl.sha256` (`Bridge.sha256_bridge`) ↔ `UInt32` `Fast.sha256` (`Api.sha256_spec`), **plus 445-line `Hash/Sha256/Context.lean`** proving `Context.init`, `update`, `finalize`, `update_append`, `Absorbs`/`Sound`, and `finalize_absorbs`. Zero `sorry`s, zero `native_decide`/`bv_decide`, `#sha256_axiom_audit` pins `[propext, Quot.sound]` (`0` `Classical.choice`), `leanchecker --fresh` in CI. | 1. **Zero HMAC** (no FIPS 198-1 / RFC 2104 anywhere in `pure-algebra/*`).<br>2. **Not zero-copy:** `Context.update` (`Context.lean:218`) allocates `c.buffer ++ chunk` ($O(\|\text{chunk}\|)$ copy on every `update`), and `Fast.lean` allocates a 64-word `Vector UInt32 64` per block rather than an unboxed `State32` + 16-word ring buffer.<br>3. **No `< 2^61` FIPS length guard:** silently wraps bit-length mod $2^{64}$ (`Context.absorbedBlocks : Nat` unbounded).<br>4. **No padding injectivity / suffix-freeness** (explicitly disclaimed at `README.md:64`).<br>5. **No arbitrary-IV `ModelsFrom` or `Midstate` API**; only 5 in-kernel CAVP KATs. |
| **2. `kim-em/lean-crypto-hash`** (Kim Morrison)<br>**[PARTIAL OVERLAP ON STREAMING API]** | [Repo](https://github.com/kim-em/lean-crypto-hash) (`master`, pushed `2026-10-22`), `README.md`, `Crypto/HMAC.lean`, `Crypto/Hash/Streaming.lean`, `validation/CryptoValidation/Proofs.lean` | **`Apache-2.0`** · **Zero root deps** · rolling `lean4` (`v4.33+`) | Pure-Lean bounded-buffer streaming (`Context.init`/`update`/`finalize`) for MD5, SHA-1, all 6 SHA-2 variants, SHA-3, SHAKE, **and streaming `Crypto.HMAC` over all 6 SHA-2 variants**, proving `digest_chunking`, `hmac_chunking`, `updateBufferedFast_eq` (slice streaming = byte fold), padding alignment/prefix preservation, and CLI differential tests against 8,332 NIST CAVP/ACVP records + OpenSSL. | 1. **Implementation-as-spec only (`README.md:188` verbatim: *"These are not a formal end-to-end proof of each compression function"*):** no separate bitwise FIPS 180-4 spec and no mathematical FIPS 198-1 `hmacSpec` equivalence.<br>2. `HMAC.Context.finalize` (`Crypto/HMAC.lean:163`) allocates `outer ++ inner.finalize.toByteArray` (no reusable `PreparedKey` `istate`/`ostate` midstates).<br>3. `validation/CryptoValidation/Proofs.lean:152,163,173` uses `bv_decide` (`Lean.ofReduceBool`). |
| **3. `pyca/verified-garbage`** (Alex Gaynor & Paul Kehrer)<br>**[ADJACENT — ISA ASSEMBLY]** | [Repo](https://github.com/pyca/verified-garbage) (pushed `2026-10-27T03:09:32Z`), `README.md`, `lean/README.md`, `lean/VerifiedGarbage/Spec/{Sha256,Hmac}.lean`, `Spec/Hmac/Generic.lean` | **`Apache-2.0 OR BSD-3-Clause`** · **Requires `Mathlib`** · `leanprover/lean4:v4.35.0` | Trusted byte-level `VG.Spec.Sha256` (including `ReprFrom iv mem p m` on 96B memory buffers) and `VG.Spec.Hmac`, verifying **machine-code/assembly ASTs** (`x86-64`, `ARM64`, `ARMv7`, `x86`, `PPC64LE`, `RISC-V`) emitted into Rust `src/asm/` (`vg_sha256_init`/`update`/`finalize`, `vg_hmac_sha256_*`) under `#assert_standard_axioms` (no `sorry`/`native_decide`). | 1. **Not a callable pure-Lean library:** `Impl/` consists of target assembly programs over `TCB.Mem` emitted as Rust `naked` functions; Lean callers cannot execute `VG.Impl` on `ByteArray`.<br>2. **Pulls full `Mathlib`** (`lean/README.md:151`) on `v4.35.0`.<br>3. Byte-only `Spec` (`Spec/Sha256.lean:10–12, 94–97`) with mod-$2^{64}$ length wraparound and no padding injectivity/suffix-freeness. |
| **4. Other repositories checked** | `remix7531/{fips-180-4-lean,hashes-fv}` (unchanged since `2026-05-26/28`); `LorenaLabs/lema-lang` (still HTTP `404`); `cryspen/libcrux` (`main` tree has `.lean` files only for SHA-3 `specs/sha3/proofs/aeneas-lean/`); `el-ev/sha256-lean`, `proofinity-it/CA`, `febyeji/lean-hash160`, `theoriclabs/leancrypto`, `Verdifax/lean-verdifax`, `typednotes/liaison`, `powdr-labs/eip8200-challenges`, `thryec/zkgolf` | Mixed (`MIT`, `Apache-2.0`, `GPL-3.0`, `NOASSERTION`) | `el-ev/sha256-lean` has unverified `Sha256.new`/`update`/`finalize` (0 theorems); `CA` & `lean-hash160` have unverified one-shot `SHA256.lean` (0 theorems); `leancrypto` wraps OpenSSL 3 FFI (0 proofs); `verdifax`, `liaison`, `eip8200-challenges` (Blake2f), `zkgolf` (Keccak) contain no SHA-256/HMAC equivalence proofs. | None of these eight repositories add verified streaming SHA-256 or verified HMAC-SHA-256 in Lean 4. |

#### Strategic Impact Assessment on M1 (Coordinator Decision Gate)

- **What is KILLED as a "first-in-Lean-4" headline claim:** Claiming the *first* permissive, zero-dependency, standard-axioms streaming SHA-256 (`init`/`update`/`finalize`) proved equivalent to FIPS 180-4 in Lean 4 is **refuted** by `pure-algebra/lean4-hash` (`MIT`, zero-dep, `[propext, Quot.sound]`, green CI as of `2026-10-11`).
- **What REMAINS genuinely open in pure, zero-dependency Lean 4:**
  1. **Two-level verified `HMAC-SHA-256` (FIPS 198-1 / RFC 2104) — both one-shot and zero-copy `PreparedKey` midstate (`istate`/`ostate`) streaming (`M5` + `M1`'s `Spec/HMAC.lean`):** Open across all pure-Lean repos (`lean4-hash` has no HMAC; `kim-em/lean-crypto-hash` has no FIPS 180-4 / 198-1 compression/spec proof and allocates `outer ++ inner`; `pyca/verified-garbage` verifies Rust assembly with Mathlib rather than pure Lean).
  2. **True zero-copy slice streaming (`update` without `c.buffer ++ chunk` full-input copy) + unboxed scalar 16-word circular ring-buffer schedule + strict `< 2^61`-byte FIPS 180-4 domain enforcement (`finalize?`) + proved padding injectivity & Merkle–Damgård suffix-freeness (`padBits_injective`, `padBits_suffix_free`) + public `Midstate` export/import + full 65-vector CAVP / 7-vector RFC 4231 in-kernel `decide +kernel` KATs.**
- **Three concrete options for programme leadership before cutting `pins/<slug>.md`:**
  1. **Redirect / Shelve Standalone SHA-256 Rebuild:** If re-proving SHA-256 (`M1`–`M4`) purely for the zero-copy ring-buffer + `< 2^61` guard + domain-separation delta over MIT `pure-algebra/lean4-hash` is below the programme's novelty threshold, **close the SHA-256 cluster** or pivot lanes to uncrowded Software-shelf targets.
  2. **Extend or Layer Above MIT `pure-algebra/lean4-hash` (Fastest Permissive Path to Open HMAC + Domain Separation):** Because `pure-algebra/lean4-hash` is `MIT` and zero-dependency (requiring only a 1-minor bump `v4.33.1 → v4.34.1`), a lane can legally layer **two-level FIPS 198-1 Midstate/Streaming `HMAC-SHA-256`**, `padBits_injective` / `padBits_suffix_free`, `< 2^61` checked wrappers, and zero-copy slice absorption on top of it (with MIT copyright preservation), cutting effort by ~50–60%.
  3. **Execute Clean-Room `Apache-2.0` M1–M6 as Pinned in §3:** Justified only if the programme explicitly wants a self-contained, `Apache-2.0`-only, zero-copy scalar ring-buffer + midstate streaming SHA-256 & HMAC-SHA-256 reference package on `v4.34.1`.

---

### 5.2 License Contamination Risks (`GPL-3.0-or-later` `fips-180-4-lean` & `LGPL-3.0` `LeanSha256`)

1. **Direct Lake import is legally incompatible with outbound `Apache-2.0`:**
   `remix7531/fips-180-4-lean` (`LICENSE`: `GPL-3.0-or-later`), `remix7531/hashes-fv`'s Lean proof tree (`sha2/proofs/lean/`: `GPL-3.0-or-later`), and `proofbundle/lean-*` headers (`GPL-3.0-or-later`) carry strong copyleft, while `etheorem/LeanSha256` and `SizzLean` carry `LGPL-3.0`. Note the one-way FSF/Apache license asymmetry: `Apache-2.0` code may be incorporated into a `GPL-3.0` project, **never the reverse** — importing `fips-180-4-lean` forces the combined work to `GPL-3.0-or-later` (exactly as happened to `remix7531/hashes-fv`).
2. **Indirect agent-context / proof-translation contamination (Chinese-wall risk):**
   Even with zero `lakefile` dependencies, if a proof-lane agent reads `remix7531/fips-180-4-lean` during proof construction (specifically its 23 `equiv/` modules such as `MatchAfter` in `equiv/SHA256/Compress/Match.lean` or `equiv/SHA256/Padding/*.lean`) and mirrors its non-functional module decomposition, identifier naming, or proof scripts, the resulting proofs face derivative-work taint risks. By contrast, NIST FIPS PUB 180-4 and FIPS PUB 198-1 are public-domain U.S. Government works (17 U.S.C. § 105), and RFC 2104 / RFC 4231 mathematical formulas are uncopyrightable standard specifications.
3. **Mandatory Clean-Room Firewall Rules for Future Proof Lanes:**
   - **No GPL/LGPL source exposure in lane prompts or pins:** `BRIEF.md` and `pins/<slug>.md` for any authoring lane must contain **zero** code excerpts, lemma names, or URLs pointing into `remix7531/fips-180-4-lean`, `remix7531/hashes-fv`, `etheorem/*`, or `proofbundle/*`.
   - **Explicit blocklist in authoring-lane working rules:** Forbid proof lanes from fetching, searching, or reading any `GPL`/`LGPL`/`NOASSERTION` SHA-2 repository during implementation and proving.
   - **Third-party MIT/BSD/Apache-2.0 hygiene:** Even permissive repos (`pure-algebra/lean4-hash` [MIT], `kim-em/lean-crypto-hash` [Apache-2.0], `pyca/verified-garbage` [Apache-2.0/BSD-3-Clause], `keithadler/lean-x509` [MIT]) require preserving upstream copyright/license notices if any code or proof structure is adapted (`pure-algebra/lean4-hash/Hash/Sha256/Context.lean:20–26` models good practice by explicitly recording reading `kim-em/lean-crypto-hash` even when no code was copied). Pure clean-room derivation from NIST PDFs + Lean `v4.34.1` `Init` avoids third-party license notice obligations altogether.

---

### 5.3 Unresolved Questions (Listed Plainly)

1. **Coordinator Go / Extend / Kill decision given `pure-algebra/lean4-hash` (Unresolved — programme policy):** Whether the discovery that `pure-algebra/lean4-hash` (`MIT`, zero-dep, `[propext, Quot.sound]`) already proves non-zero-copy `Context` streaming SHA-256 against bit-level FIPS 180-4 leads programme leadership to (a) cancel standalone `M1`–`M4` SHA-256 work, (b) pivot directly to two-level zero-copy Midstate/Streaming `HMAC-SHA-256` + domain separation + `< 2^61` guard, or (c) proceed with clean-room `Apache-2.0` `M1`–`M6`.
2. **Pin Boundary Selection — Scope A (`Spec/` + Anchor KATs) vs. Scope B (Consolidated End-to-End Streaming SHA-256) (Unresolved — coordinator pin choice):** Whether `~/workspace/math-fleet/pins/<slug>.md` for `M1` freezes Part 3A alone (+ anchor KATs) to unlock parallel `M2`/`M3` lanes, or freezes Part 3A + Part 3B together as a single end-to-end Streaming SHA-256 pin.
3. **Target repository placement (`repo:` field in `pin-manifest-template.md`) (Unresolved — coordinator choice):** Which target repository (`derekblair/formalize-everything` vs. a standalone Apache-2.0 crypto package repo) hosts `statement_file.path` and at which initial commit `statement_file.commit` will be hashed.
4. **Public exposure vs. internal-only `Midstate` API (Unresolved — API design choice):** Whether `Hasher.exportMidstate?` / `Hasher.fromMidstate?` (Theorems B5–B6) should be part of the public `Sha256.Impl` surface (useful for checkpointing and Bitcoin/digest-prefix caching, with documented Merkle–Damgård length-extension caveats) or kept module-private for `M5`'s `PreparedKey` HMAC engine.
5. **Closed / unreleased `LorenaLabs/lema-lang` object store (`UNVERIFIED`):** `https://github.com/LorenaLabs/lema-lang` continues to return `HTTP 404` on `2026-10-27` (`LorenaLabs`'s 14 public GitHub repos contain Rust staging forks and agent skills, not `lema-lang`); its documented one-shot `Sha256Unboxed` and `Std.Crypto.Hmac` theorems and axiom footprints remain uninspectable.
6. **Exact `v4.34.1` kernel wall-clock threshold on multi-KB `decide +kernel` vectors (`UNVERIFIED` locally):** Because research-only rules forbid writing or compiling Lean code in this lane, the exact `maxHeartbeats` / memory crossover point for `decide +kernel` over `KernelEval.sha256Nat` on `leanprover/lean4:v4.34.1` (estimated at ~150–300 blocks / 10–19 KiB from `keithadler/lean-x509`'s X.509 chain certificates on `v4.35.0`) was not benchmarked locally here.

---

### What This Dossier Does NOT Show

This dossier is a strictly read-only research and statement-pinning preparation artifact produced on 2026-10-27 without writing, elaborating, or compiling any Lean 4 code (`lake build` was never run). Consequently, while every Lean `Init` identifier in Section 3 was cross-checked against `leanprover/lean4` tag `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) source files on GitHub, the proposed Lean code blocks in Section 3 have **not yet been machine-elaborated by the `v4.34.1` typechecker**, and our prior-art verdicts on `pure-algebra/lean4-hash`, `kim-em/lean-crypto-hash`, and `pyca/verified-garbage` rest on direct source inspection plus public GitHub Actions metadata rather than local proof replay (`LorenaLabs/lema-lang` remains `UNVERIFIED` due to `HTTP 404`). Finally, this dossier prepares — and does **not** itself constitute — the frozen pin manifest `~/workspace/math-fleet/pins/<slug>.md`, nor do any of the pinned functional-equivalence statements establish computational collision resistance, PRF unforgeability, C-compiler/runtime correctness, or hardware side-channel / constant-time guarantees.

DOSSIER COMPLETE
