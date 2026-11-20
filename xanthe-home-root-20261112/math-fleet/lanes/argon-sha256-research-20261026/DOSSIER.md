# Research Dossier: SHA-256 Two-Level Formalization & Remaining Open Targets in Lean 4

- **Lane:** `argon-sha256-research-20261026`
- **Date:** 2026-10-27
- **Mode:** Research-only primary-source audit (zero repo clones, zero code/GitHub writes)
- **Prior-art baseline reviewed in full:** `prior-art-sha256.md` (lines 1–132, including the `2026-10-26` `ERRATUM`)

---

## Executive Verdict

1. **Closing `formalize-everything` ticket `#17` (pure-Lean two-level SHA-256 formalization) was unequivocally RIGHT — in fact, doubly right.** Primary-source inspection of GitHub repositories confirms that **two independent pure-Lean two-level SHA-256 + SHA-224 formalizations** already exist at the kernel bar, alongside a third Aeneas-extracted Rust-to-Lean proof:
   - **`remix7531/fips-180-4-lean`** (`0018b08f34`, May 2026, GPL-3.0-or-later, Lean `v4.29.1` + Mathlib): separate literate bit-level `spec/` and unrolled ring-buffer machine-word `impl/`, with kernel-checked `compress_correct`, `sha256_correct`, and `sha224_correct` (plus the SHA-512 family) pinned by `#guard_msgs in #print axioms` to `[propext, Classical.choice, Quot.sound]`, zero `sorry`s, and green GitHub Actions CI.
   - **`pure-algebra/lean4-hash`** (`ab7eda433f`, October 2026, **MIT**, Lean `v4.33.1`, **zero external dependencies**): missed by both the original `prior-art-sha256.md` pass and its `ERRATUM`. Provides a bit-level FIPS 180-4 transcription (`Hash.Sha256.Spec`), byte-level `BitVec 32` reference (`Impl`), native `UInt32`/`ByteArray` engine (`Fast`), **SHA-224** (`Sha224`), **and an incremental streaming `Context` (`init`/`update`/`finalize`)** proved equivalent to one-shot SHA-256 (`finalize_absorbs`, `sha256_spec`), with all 420 SHA-256 declarations audited under `[propext, Quot.sound]` (`0` reach `Classical.choice`, zero `sorry`s, rechecked by `leanchecker --fresh` in CI).
   - **`sha2-fv` → located at `remix7531/hashes-fv`** (`5b33fdba3e`, May 2026, Rust crate MIT/Apache-2.0, Lean proofs GPL-3.0-or-later): Charon + Aeneas extraction of a stripped one-shot fork of RustCrypto `sha2` refined against `remix7531/fips-180-4-lean` (`sha256_spec`, `sha224_spec`, plus SHA-512 family), zero `sorry`s in committed `.lean` files, though carrying an extra Aeneas standard-library formatting axiom (`Aeneas.Std.core.fmt.Formatter`) and Cargo-only CI.
2. **Verdict on the standing claim** (*"LeanSha256 is implementation-as-spec AND the two-level spec+equivalence artifact is open"*):
   - **Conjunct 1 (*"LeanSha256 is implementation-as-spec"*): `CONFIRMED`.** Primary source `etheorem/etheorem` (`packages/LeanSha256/LeanSha256/Core.lean` `@ 3d56ad2525`) contains a single computational `UInt32`/`ByteArray` implementation, explicitly disclaims proving SHA-256 correctness in its module docstring (*"These don't claim 'computes SHA-256'. That's an empirical claim the NIST asserts settle."*), proves only 17 structural/size-preservation lemmas, and gates its 3 core + 129 CAVP test vectors via `native_decide` (`Lean.ofReduceBool`).
   - **Conjunct 2 (*"the two-level spec+equivalence artifact is open in Lean"*): `REFUTED`.** Both `remix7531/fips-180-4-lean` and `pure-algebra/lean4-hash` deliver genuine two-level FIPS 180-4 bit-spec ↔ `UInt32`/`ByteArray` implementation equivalence proofs under standard kernel axioms.
3. **What actually remains open (and what is already taken or logically impossible among candidate follow-ups):**
   - *SHA-224:* **TAKEN** (proved in both `remix7531/fips-180-4-lean` and `pure-algebra/lean4-hash`, plus `hashes-fv`).
   - *Standalone importable SHA-256 spec+impl library:* **TAKEN** (`pure-algebra/lean4-hash`, MIT, zero dependencies).
   - *Streaming `init`/`update`/`finalize` SHA-256 proved equivalent to one-shot spec:* **TAKEN** (`pure-algebra/lean4-hash/Hash/Sha256/Context.lean`).
   - *Discharging SizzLean's three `*_eq_spec` FFI-bridge axioms as stated:* **IMPOSSIBLE IN LEAN'S LOGIC** without replacing FFI, because `LeanHazmatSha256/Ffi.lean` declares `sha256Hash`, `sha256Combine`, and `sha256BatchCombine` as `@[extern "lean_hazmat_..."] opaque` constants with no kernel body; equality between an `opaque` constant and `LeanSha256.hash` is independent of Lean's kernel axioms (only a pure-Lean `@[csimp]` replacement theorem is provable).
   - **Strongest genuinely OPEN SHA-256-adjacent artifact:** **Two-level pure-Lean `HMAC-SHA-256` (FIPS 198-1 / RFC 2104) and `HKDF-SHA-256` (RFC 5869) constructions proved over a FIPS 180-4 SHA-256 specification — including NMAC 1-block key-midstate precomputation and streaming `init`/`update`/`finalize` HMAC equivalence — at the kernel bar (`[propext, Quot.sound]` / `[propext, Classical.choice, Quot.sound]`, zero `native_decide`).** Every standalone Lean HMAC library today (`kim-em/lean-crypto-hash`, `paulbutcher/leancrypto`, `SentinelOps-CI/lean-toolchain`) is explicitly implementation-as-spec, `proofbundle/lean-{hmac,hkdf}-sha-256` are empty `"NOT_IMPLEMENTED"` scaffolds, and `Beneficial-AI-Foundation/libsignal-verify` PR #43 (merged `2026-10-26`) had to axiomatize `HmacSha256` as an uninstantiated structure interface (*"Prose only. Lean proves just that tags have 32 bytes"*).

---

## 1. Prior-Art Sweep (Testing the Standing Claim)

### 1.1 Primary-Source Audit #1: `remix7531/fips-180-4-lean`

- **Repository & metadata:** `https://github.com/remix7531/fips-180-4-lean`, inspected at `main` HEAD `0018b08f3458553ad511e92a96336979c1e0c45a` (repo metadata via `https://api.github.com/repos/remix7531/fips-180-4-lean` and commit/workflow logs via `https://api.github.com/repos/remix7531/fips-180-4-lean/actions/runs`).
  - **Activity / maintenance state:** Created `2026-04-20`; active burst through last push `2026-05-26T08:19:54Z`; **dormant for 5 months** since May 26, 2026 (`0` stars, `0` forks, `0` open issues/PRs).
  - **Toolchain & dependencies:** Lean `leanprover/lean4:v4.29.1` (`lean-toolchain`), `lakefile.toml` requires **Mathlib** (`leanprover-community/mathlib4 @ v4.29.1`) and `mdgen` (`seasawher/mdgen`, literate Markdown generation). Total size: 57 `.lean` files (9,702 lines across `spec/`, `impl/`, `equiv/`, `tests/`).
  - **License:** **`GPL-3.0-or-later`** (`https://raw.githubusercontent.com/remix7531/fips-180-4-lean/0018b08f3458553ad511e92a96336979c1e0c45a/LICENSE` — full GNU General Public License v3 text; `lakefile.toml` also declares `license = "GPL-3.0-or-later"`). Note: strong copyleft prevents linking into Apache-2.0 / MIT / LGPL-3.0-only downstream repos without relicensing.

- **Exact theorem statements (`equiv/SHA256/Main.lean`):**
  Read directly from `https://raw.githubusercontent.com/remix7531/fips-180-4-lean/0018b08f3458553ad511e92a96336979c1e0c45a/equiv/SHA256/Main.lean` (lines 38–83):
  ```lean
  theorem compress_correct (state : Impl.State) (block : Impl.Block) :
      toSpecState (Impl.compress state block) =
        SHS.SHA256.compress (toSpecState state) (toSpecBlock block)

  theorem sha256_correct (data : ByteArray) (h : data.size < 2 ^ 61) :
      digestBitVec (Impl.sha256 data) =
        SHS.SHA256.sha256 (bytesToBitMessage data) (bitLen_lt_of_size_lt data h)

  theorem sha224_correct (data : ByteArray) (h : data.size < 2 ^ 61) :
      digestBitVec224 (Impl.sha224 data) =
        SHS.SHA256.sha224 (bytesToBitMessage data) (bitLen_lt_of_size_lt data h)
  ```
  (Parallel theorems `compress_correct`, `sha512_correct`, `sha384_correct`, `sha512_256_correct`, and `sha512_224_correct` are proved in `equiv/SHA512/Main.lean`.)

- **Are `spec/` and `impl/` genuinely independent?** **YES — completely distinct data types, memory layouts, schedules, and control flow.**
  - **`spec/`** (inspected `spec/Setup.lean`, `spec/Notation.lean`, `spec/Functions.lean`, `spec/Preprocessing.lean`, `spec/HashAlgorithms.lean`, `spec/SHA512t.lean` at `0018b08f34`): Literate section-by-section transcription of NIST FIPS 180-4. Represents messages at **bit granularity** (`abbrev Message := List Bool`), words as `BitVec 32` (`abbrev Word (w : Nat) := BitVec w`), blocks as `Vector (BitVec 32) 16`, and schedules as a full 64-word `Vector (BitVec 32) 64`. `SHS.SHA256.pad` computes `k` as the minimal solution to `ℓ + 1 + k ≡ 448 [MOD 512]` and appends the 64-bit big-endian bit list of `ℓ`; `parse` slices bit lists into 512-bit/32-bit chunks via `Word.fromBits`; `SHS.SHA256.sha256 (M : Message) (_h : M.length < 2 ^ 64) : Digest 256` folds `SHS.SHA256.compress` from `H0_256` and concatenates `H[0] ++ H[1] ++ ... ++ H[7]` into `BitVec 256`.
  - **`impl/`** (inspected `impl/SHA256.lean` and `impl/Unroll.lean` at `0018b08f34`): High-throughput (~170 MiB/s benchmarked in `README.md`) byte-and-`UInt32` code. `RoundState` stores eight scalar `UInt32` registers (`a b c d e f g h : UInt32`) plus a **16-word ring buffer** `w : Vector UInt32 16` updated in-place modulo 16 (`roundStep`) rather than allocating a 64-word schedule; `Impl.compress` executes a **64-way compile-time unrolled pipeline** (`SHS.Impl.Unroll.unroll64`); `toU32sFromBytes` decodes four `UInt8` offsets directly from `ByteArray`; and finalization splits on `remaining < 56` vs `remaining ≥ 56` to construct one or two trailing 64-byte blocks directly in bytes (guarding `if 2 ^ 61 ≤ data.size then panic!`).
  - **`equiv/`** requires 20 files of genuine refinement bridges (`equiv/SHA256/Compress/{Schedule,Step,Round,Unroll,Impl,Match}.lean`, `equiv/SHA256/Padding/{ByteDecoding,Layout,Parsing,Equiv}.lean`, `equiv/SHA256/{Lift,Digest,Foldl,Pipeline,Main}.lean`) to connect the 16-slot ring buffer to the 64-word schedule and byte-level two-branch padding to bit-level modular padding.

- **`sorry` / axiom / CI status:**
  - Full regex audit across all 57 `.lean` files in the tarball `https://codeload.github.com/remix7531/fips-180-4-lean/tar.gz/0018b08f3458553ad511e92a96336979c1e0c45a`: **0 `sorry`**, **0 `admit`**, **0 `axiom`**, **0 `opaque`**, **0 `@[extern]`**, **0 `unsafe`**, **0 `partial`**.
  - Only **2 occurrences of `native_decide`** exist in the entire repo, both isolated in `spec/SHA512t.lean` (lines 72 and 102, checking FIPS 180-4 §5.3.6's SHA-512/t IV generation for `H0_512_224_correct` and `H0_512_256_correct`). `spec/SHA512t.lean` is **not imported** by `equiv/SHA256/Main.lean` or `equiv/SHA512/Main.lean`.
  - **`equiv/AxiomCheck.lean`** (read in full at `https://raw.githubusercontent.com/remix7531/fips-180-4-lean/0018b08f3458553ad511e92a96336979c1e0c45a/equiv/AxiomCheck.lean`) enforces `#guard_msgs in #print axioms` on all 8 public theorems (`sha256_correct`, `compress_correct`, `sha224_correct`, `sha512_correct`, `SHA512.compress_correct`, `sha384_correct`, `sha512_256_correct`, `sha512_224_correct`), pinning each to `[propext, Classical.choice, Quot.sound]`.
  - **CI verification:** `.github/workflows/lean_action_ci.yml` invokes `leanprover/lean-action@v1` with `build-args: "spec impl equiv tests"` and `lint: "true"`. GitHub Actions API (`https://api.github.com/repos/remix7531/fips-180-4-lean/actions/runs?per_page=5`) confirms workflow run `26441432411` on HEAD `0018b08f34` completed with `conclusion: "success"` at `2026-05-26T08:31:58Z`.

- **Scope:**
  - **One-shot vs streaming:** **One-shot `ByteArray → Vector UInt8 32` only** (plus bit-level `Message → Digest 256` in `spec/`). No incremental `Context` (`init`/`update`/`finalize`) exists anywhere in the repo.
  - **Padding proved?** **Yes** (`equiv/SHA256/Padding/Equiv.lean`: `implPaddedBlocks_lift_eq_parsePad` proves byte-level two-branch padding + block decoding equals `SHS.SHA256.parse (SHS.SHA256.pad (bytesToBitMessage data))` for all `data.size < 2 ^ 61`).
  - **SHA-224 included?** **Yes** (`SHS.SHA256.sha224` in `spec/HashAlgorithms.lean`, `Impl.sha224` in `impl/SHA256.lean`, and `sha224_correct` in `equiv/SHA256/Main.lean`).
  - **SHA-1 note:** `spec/` defines `SHS.SHA1.sha1`, and `tests/CAVP.lean` tests it on CAVP vectors, **but no `impl/SHA1.lean` or `equiv/SHA1` exists**.
  - **HMAC / HKDF:** None.

---

### 1.2 Primary-Source Audit #2: `sha2-fv` (`remix7531/hashes-fv`)

- **Locating the repository:** Querying the crates.io API directly at `https://crates.io/api/v1/crates/sha2-fv` resolved the listing unambiguously:
  - **Repository:** `https://github.com/remix7531/hashes-fv` (same author `remix7531` as `fips-180-4-lean`!), `main` HEAD `5b33fdba3e77dceca487e35bc65610758d00b40c`.
  - **Crate version & activity:** `v0.1.0` published `2026-05-28T09:00:57Z`; repo created `2026-05-26`, last push `2026-05-28T09:16:38Z` (**dormant since May 28, 2026**; `0` stars, `0` forks).
  - **Architecture:** A stripped fork of RustCrypto's `sha2` crate (`sha2/src/`), keeping **only** the portable `soft-compact` Rust backend and **removing RustCrypto's streaming `Digest` trait (`Update`/`FixedOutput`)** in favor of six one-shot functions (`pub fn sha256(data: &[u8]) -> [u8; 32]`, `sha224`, `sha512`, `sha384`, `sha512_256`, `sha512_224` in `sha2/src/lib.rs`). Translated from Rust MIR to Lean 4 (`v4.29.1`) via Charon + Aeneas (`https://github.com/remix7531/aeneas` branch `sha2-fv-pin`) and refined against `remix7531/fips-180-4-lean` (`rev = "0018b08f34..."` in `sha2/proofs/lean/lakefile.toml`).
  - **License split:** Rust crate (`sha2/Cargo.toml`) is `MIT OR Apache-2.0`, whereas the Lean proof package (`sha2/proofs/lean/lakefile.toml` and `sha2/proofs/lean/LICENSE`) is **`GPL-3.0-or-later`** (inherited from importing `fips-180-4-lean`).

- **Exact theorem statements (`sha2/proofs/lean/Sha256.lean`):**
  Read directly from `https://raw.githubusercontent.com/remix7531/hashes-fv/5b33fdba3e77dceca487e35bc65610758d00b40c/sha2/proofs/lean/Sha256.lean` (lines 19–45):
  ```lean
  theorem sha256_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
      Extraction.sha256 data
      ⦃ out =>
          let hb := bytesToBits_length_lt_2_64 data.val h
          SHS.Word.fromBits (bytesToBits out.val) =
            SHS.SHA256.sha256 (bytesToBits data.val) hb ⦄

  theorem sha224_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
      Extraction.sha224 data
      ⦃ out =>
          let hb := bytesToBits_length_lt_2_64 data.val h
          SHS.Word.fromBits (bytesToBits out.val) =
            SHS.SHA256.sha224 (bytesToBits data.val) hb ⦄
  ```
  (Here `e ⦃ out => P out ⦄` is Aeneas's weakest-precondition Hoare postcondition over `Result`, proving both panic-freedom/termination on `data.length < 2 ^ 61` and bitwise equality with `SHS.SHA256.sha256` from `fips-180-4-lean`. Parallel theorems `sha512_spec`, `sha384_spec`, `sha512_256_spec`, and `sha512_224_spec` appear in `sha2/proofs/lean/Sha512.lean`.)

- **`sorry` / axiom / build caveats (three primary-source findings hidden behind the crates.io listing):**
  1. **Zero `sorry`s in committed `.lean` files:** Tarball scan of all 35 committed `.lean` files (5,143 lines) in `https://codeload.github.com/remix7531/hashes-fv/tar.gz/5b33fdba3e77dceca487e35bc65610758d00b40c` found **0 `sorry`**, **0 `admit`**, **0 `native_decide`**.
  2. **Non-standard 4th axiom (`Aeneas.Std.core.fmt.Formatter`):** Read directly in `sha2/proofs/lean/AxiomCheck.lean` (`https://raw.githubusercontent.com/remix7531/hashes-fv/5b33fdba3e77dceca487e35bc65610758d00b40c/sha2/proofs/lean/AxiomCheck.lean`): its module docstring explicitly documents that all six `*_spec` theorems depend on **`[propext, Classical.choice, Quot.sound, Aeneas.Std.core.fmt.Formatter]`** because Rust's `chunk.try_into().unwrap()` pulls in `core::fmt::Formatter` as an Aeneas `axiom` in dead panic branches. Furthermore, `AxiomCheck.lean` invokes bare `#print axioms` **without `#guard_msgs`**, so axiom regressions would not break elaboration.
  3. **Uncommitted `Extraction/` & Cargo-only CI:** `.gitignore` excludes `sha2/proofs/lean/Extraction/` (generated by running Nix + Charon + Aeneas via `Makefile`), and `.github/workflows/sha2.yml` runs only `cargo build`, `cargo test`, and `cargo fmt` — **Lean proofs (`make prove` / `lake build`) are NOT executed in GitHub Actions CI** (so end-to-end replay of `Extraction.*` against `Sha256.lean` could not be verified from CI logs and is marked **`UNVERIFIED` without local Nix+Aeneas execution**, though the proof scripts themselves contain zero `sorry`s).

---

### 1.3 Major New Discovery #3: `pure-algebra/lean4-hash` (October 2026)

Neither `prior-art-sha256.md` nor its `2026-10-26` `ERRATUM` surfaced **`pure-algebra/lean4-hash`**, which directly impacts nearly every candidate follow-up in Section 2:

- **Repository & metadata:** `https://github.com/pure-algebra/lean4-hash`, inspected at `main` HEAD `ab7eda433f0390fde7aa240189761540c9744c79` (`https://api.github.com/repos/pure-algebra/lean4-hash`).
  - **Activity & toolchain:** Created `2026-09-02`, actively developed through `2026-10-11T21:44:22Z`; targets Lean **`leanprover/lean4:v4.33.1`** (`lean-toolchain`), uses Lean's new `module` system, has **zero external dependencies** (`lakefile.toml` / `lake-manifest.json`), and is licensed under **`MIT`** (`LICENSE`).
  - **Scope:** Covers **SHA-256**, **SHA-224**, **incremental streaming SHA-256 (`Hash.Sha256.Context`)**, and **SHA3-512** (FIPS 202).
  - **Three-layer SHA-256 architecture + exact theorems** (read directly from `Hash/Sha256/Spec.lean`, `Hash/Sha256/Api.lean`, `Hash/Sha256/Context.lean`, `Hash/Sha256/Sha224.lean`, and `Hash/Sha256/Verified.lean` at `ab7eda433f`):
    - `Hash.Sha256.Spec` (`Spec.lean`): Bit-level (`List Bool` / `BitVec 32` / `Vector Word 64`) transcription of FIPS 180-4 (`Ch`, `Maj`, `Σ0`, `Σ1`, `σ0`, `σ1`, `K`, `H0`, `pad`, `parse`, `schedule`, `compress`, `sha256`, `sha256_bytes`).
    - `Hash.Sha256.Impl` & `Hash.Sha256.Bridge`: Byte-level `List UInt8` / `BitVec 32` reference proved equal to `Spec.sha256_bytes` (`Bridge.sha256_bridge`).
    - `Hash.Sha256.Fast` & `Hash.Sha256.Api`: Native `ByteArray` / `UInt32` implementation proved equal to `Impl` and `Spec`:
      ```lean
      theorem sha256_spec (msg : ByteArray) :
          (sha256 msg).toList = Spec.sha256_bytes msg.data.toList
      theorem sha224_spec (msg : ByteArray) :
          (sha224 msg).toList = Sha224.Spec.sha224_bytes msg.data.toList
      ```
    - `Hash.Sha256.Context` (`Context.lean`): Streaming state `{ state : Vector UInt32 8, buffer : ByteArray, buffer_lt : buffer.size < 64, absorbedBlocks : Nat }` with `init`, `update`, `finalize`, proving chunk-split invariance (`update_empty`, `update_append`) and one-shot equivalence:
      ```lean
      theorem finalize_absorbs {c : Context} {bs : List UInt8} (h : Absorbs c bs) :
          c.finalize.toList = Impl.sha256 bs
      theorem finalize_init_update (m : ByteArray) : (init.update m).finalize = sha256 m
      ```
  - **Axiom & `leanchecker` audit:** `Hash/Sha256/Verified.lean` runs `#guard_msgs in #sha256_axiom_audit`, verifying across all **420 public declarations in 12 modules** that **only `[propext, Quot.sound]`** are used (`0 reach Classical.choice`, `0` `sorry`s, `0` `native_decide`, plus 1 kernel-reduced KAT `theorem kernel_kat_w1 : Impl.sha256 w1Msg = w1Digest := by decide +kernel` in `Hash/Sha256/Kats.lean`). GitHub Actions workflow `.github/workflows/ci.yml` runs `lake build` and **`lake env leanchecker --fresh Hash.Verified`**, succeeding on HEAD `ab7eda433f` (`run 38143123695`).
  - **One technical caveat found in primary source (`Spec.lean:155–158`)**: `Spec.pad` writes `bitsOfNat 64 M.length` without a `< 2^64` bit-length precondition (`natOfBits_bitsOfNat : natOfBits (bitsOfNat k n) = n % 2 ^ k`), silently reducing `M.length mod 2^64` for messages `≥ 2^61` bytes so `sha256_spec` holds unconditionally by matching `Fast`'s modular length truncation, whereas FIPS 180-4 §5.1.1 restricts SHA-256's domain strictly to `0 ≤ ℓ < 2^64` bits (`msg.size < 2^61`). Also, `lean4-hash` contains **no HMAC, no HKDF, and no streaming SHA-224 context**.

---

### 1.4 Primary-Source Re-Audit of `LeanSha256` & `SizzLean` (`etheorem/etheorem`)

To test Conjunct 1 and evaluate SizzLean's axioms from primary sources rather than README summaries, we inspected `https://github.com/etheorem/etheorem` at `main` HEAD `3d56ad2525122bf5d2a79923d5fc822cd2cc53d2` (and mirror `https://github.com/etheorem/LeanSha256` at `f3432475b35714c33c2ca627eb592a55e82de6d9`):

1. **`packages/LeanSha256/LeanSha256/Core.lean`** (`https://raw.githubusercontent.com/etheorem/etheorem/3d56ad2525122bf5d2a79923d5fc822cd2cc53d2/packages/LeanSha256/LeanSha256/Core.lean`):
   - Licensed `LGPL-3.0-only`, Lean `v4.29.0`, zero dependencies.
   - Defines `hash : ByteArray → ByteArray` and `combine : ByteArray → ByteArray → ByteArray` directly over `UInt32` and `Array UInt32`. Zero `sorry`s, zero `axiom`s in `Core.lean`, **except** 3 `#guard_msgs` / `native_decide` (`decide` / `Lean.ofReduceBool`) FIPS §B example gates.
   - Lines 339–344 of `Core.lean` state verbatim:
     > *"Structural conformance theorems ... **These don't claim 'computes SHA-256'. That's an empirical claim the NIST asserts settle.**"*
   - Its 17 theorems (`ch_eq_fips`, `maj_eq_fips`, `bigSigma0_eq_fips`, `bigSigma1_eq_fips`, `smallSigma0_eq_fips`, `smallSigma1_eq_fips`, `h0_size`, `kConstants_size`, `pad_size_multiple_of_64`, `messageSchedule_size`, `messageSchedule_prefix`, `messageSchedule_step`, `compress_size`, `hash_short_msg`, `hash_size_eq_32`, `combine_eq_hash_append`, `combine_size_eq_32`) are single-layer `rfl` identities and array-size preservation checks on the implementation itself; `LeanSha256Tests/Nist.lean` checks 129 CAVP vectors via `native_decide`.
2. **`packages/SizzLean/SizzLean/Crypto/Sha256Equiv.lean` & `packages/hazmat/LeanHazmatSha256/LeanHazmatSha256/Ffi.lean`**:
   - Read directly from `https://raw.githubusercontent.com/etheorem/etheorem/3d56ad2525122bf5d2a79923d5fc822cd2cc53d2/packages/hazmat/LeanHazmatSha256/LeanHazmatSha256/Ffi.lean` and `.../packages/SizzLean/SizzLean/Crypto/Sha256Equiv.lean`:
     ```lean
     -- In LeanHazmatSha256/Ffi.lean:
     @[extern "lean_hazmat_sha256_hash"] opaque sha256Hash (data : @& ByteArray) : ByteArray
     @[extern "lean_hazmat_sha256_combine"] opaque sha256Combine (left right : @& ByteArray) : ByteArray
     @[extern "lean_hazmat_sha256_batch_combine"] opaque sha256BatchCombine (pairs : @& ByteArray) : ByteArray

     -- In SizzLean/Crypto/Sha256Equiv.lean:
     axiom sha256Hash_eq_spec (data : ByteArray) : LeanHazmatSha256.sha256Hash data = LeanSha256.hash data
     axiom sha256Combine_eq_spec (a b : ByteArray) :
         a.size = 32 → b.size = 32 → LeanHazmatSha256.sha256Combine a b = LeanSha256.combine a b
     axiom sha256BatchCombine_eq_spec (pairs : ByteArray) (n : Nat) :
         pairs.size = n * 64 → ...
     ```
   - Crucially, `sha256Hash`, `sha256Combine`, and `sha256BatchCombine` are `@[extern] opaque` C bindings (calling OpenSSL `EVP_Q_digest` and optional Intel ISA-L multi-buffer SIMD in C). They have **no Lean term body** in the kernel.

---

### 1.5 Comprehensive Cross-Ecosystem Sweep Table

#### A. Lean 4 Ecosystem (21 primary sources inspected)

| Source | URL & Commit / Ref Read | Artifact & Scope | Correctness / Axiom Status | License & Activity |
|---|---|---|---|---|
| **`remix7531/fips-180-4-lean`** | `https://github.com/remix7531/fips-180-4-lean` (`0018b08f34`, read all 57 `.lean` files + Actions API) | **Two-level pure-Lean FIPS 180-4:** bit-level `spec/` (SHA-1, 224, 256, 384, 512, 512/224, 512/256) + unrolled ring-buffer `UInt32` `impl/` (SHA-224/256/384/512/512t). One-shot `ByteArray` only; no streaming, no HMAC | **COMPLETE (one-shot):** `compress_correct`, `sha256_correct`, `sha224_correct` (+5 SHA-512 theorems) proved; 0 `sorry`, 0 `axiom`; `#guard_msgs in #print axioms` pins `[propext, Classical.choice, Quot.sound]`; CI green | `GPL-3.0-or-later`; Mathlib dep; last push `2026-05-26` |
| **`pure-algebra/lean4-hash`** | `https://github.com/pure-algebra/lean4-hash` (`ab7eda433f`, read `Spec`, `Impl`, `Bridge`, `Fast`, `Api`, `Context`, `Sha224`, `Kats`, `Verified`, CI) | **Three-layer pure-Lean FIPS 180-4 + FIPS 202:** SHA-256, SHA-224, **streaming `Sha256.Context` (`init`/`update`/`finalize`)**, and SHA3-512. Zero external deps. (`Spec.pad` wraps mod `2^64` rather than guarding `< 2^64` bits; no HMAC/HKDF) | **COMPLETE (one-shot + SHA-256 streaming):** `sha256_spec`, `sha224_spec`, `finalize_absorbs`; 420 SHA-256 decls audited under **`[propext, Quot.sound]`** (`0` `Classical.choice`, `0` `sorry`); `decide +kernel` KAT; `leanchecker --fresh` green in CI | `MIT`; zero deps; Lean `v4.33.1`; active (`2026-10-11`) |
| **`sha2-fv` (`remix7531/hashes-fv`)** | `https://crates.io/api/v1/crates/sha2-fv` → `https://github.com/remix7531/hashes-fv` (`5b33fdba3e`, read all 35 `.lean` files + Rust `src/` + CI) | Charon + Aeneas extraction of stripped one-shot RustCrypto `sha2` (`soft-compact` only; streaming `Digest` trait removed) refined against `fips-180-4-lean` (SHA-224/256/384/512/512t) | `sha256_spec`, `sha224_spec` (+4 SHA-512 specs) with 0 `sorry` in committed `.lean` files, **but** depends on 4th axiom `Aeneas.Std.core.fmt.Formatter`, unguarded `#print axioms`, `.gitignore`d `Extraction/`, Cargo-only CI (Lean replay `UNVERIFIED` in CI) | Rust: `MIT OR Apache-2.0`; Lean proofs: `GPL-3.0-or-later`; last push `2026-05-28` |
| **`LeanSha256` (`etheorem`)** | `https://github.com/etheorem/etheorem` (`3d56ad2525`, `packages/LeanSha256/LeanSha256/Core.lean`, `LeanSha256Tests/Nist.lean`) | Pure-Lean `UInt32`/`ByteArray` `hash` & `combine` (one-shot SHA-256 only) | **Implementation-as-spec:** 0 `sorry`, 17 structural/size lemmas, explicitly disclaims proving SHA-256 in `Core.lean:339–344`; 3 core + 129 CAVP vectors via `native_decide` (`Lean.ofReduceBool`) | `LGPL-3.0-only`; zero deps; active Oct 2026 |
| **`SizzLean` + `LeanHazmatSha256`** | `https://github.com/etheorem/etheorem` (`3d56ad2525`, `packages/SizzLean/.../Sha256Equiv.lean`, `packages/hazmat/.../Ffi.lean`) | Verified Ethereum SSZ Merkleization parameterized over `Sha256Spec`; OpenSSL/ISA-L C FFI fast path | Assumes 3 explicit `axiom`s (`sha256Hash_eq_spec`, `sha256Combine_eq_spec`, `sha256BatchCombine_eq_spec`) equating `@[extern] opaque` C bindings to `LeanSha256` | `LGPL-3.0-only`; active Oct 2026 |
| **`kim-em/lean-crypto-hash`** | `https://github.com/kim-em/lean-crypto-hash` (`4fa361c69f`, read `README.md`, `Crypto/SHA2.lean`, `Crypto/HMAC.lean`, `Crypto/Proofs/*`) | Pure-Lean streaming + one-shot MD5, SHA-1, SHA-2 (224/256/384/512/512t), SHA-3/SHAKE, and **HMAC-SHA-2** (`Crypto/HMAC.lean`), zero root deps (Kim Morrison) | **Implementation-as-spec:** proves streaming = one-shot (`digest_chunking`, `hmac_chunking`), padding alignment, endian roundtrips (`bv_decide`), + 8,332 CAVP/ACVP runtime vectors (1,575 HMAC). `README.md` explicitly states: *"not a formal end-to-end proof of each compression function"* (no FIPS 180-4 / 198-1 spec layer) | `Apache-2.0`; active (`2026-10-22`) |
| **`pyca/verified-garbage`** | `https://github.com/pyca/verified-garbage` (`9efc19858c`, read `README.md`, `VG/Spec/Sha256.lean`, `VG/Spec/Hmac.lean`) | Multi-ISA assembly generator + Lean machine-code proofs (x86/x86-64/ARM/AArch64/PPC64LE/RISC-V) against `VG.Spec.Sha256` and `VG.Spec.Hmac` | Verifies emitted assembly against internal `VG.Spec`; **not** a pure-Lean executable hash/MAC library; Rust wrapper is unverified and `README.md` notes long-key HMAC (`|K| > B`) hashes the key in unverified Rust; no HKDF | `Apache-2.0 OR BSD-3-Clause`; active (`2026-10-27`) |
| **`thevilledev/ocaml-pq`** | `https://github.com/thevilledev/ocaml-pq` (`ceeb2782e0`, read `formal/lean/OcamlPq/Hash/{Sha2Spec,Sha256,HmacMgf1}.lean`) | Monolithic 36k-line verification of OCaml SLH-DSA / ML-DSA (`List UInt8` model of OCaml `sha256` and `hmac_sha256`) | Proves OCaml Byte-model `sha256_bytes_eq_fips_sha256` and one-shot `hmac_sha256_eq_fips_198_1` via **`noncomputable def SHA256Bytes`** (`Classical.choose`); coupled to OCaml AST + Mathlib, not a standalone executable Lean `ByteArray` library, no midstate/streaming HMAC, no HKDF | Repo has no root `LICENSE` file inspected (`UNVERIFIED` license); active Oct 2026 |
| **`Beneficial-AI-Foundation/libsignal-verify` (PR #43)** | `https://github.com/Beneficial-AI-Foundation/libsignal-verify/pull/43` (merged `2026-10-26T22:31:17Z`, read PR body & file list `HkdfSha256.lean`) | Aeneas verification of Signal PQXDH `derive_with_label` / `derive` (96-byte 3-block `hkdfExpand96`) | **Assumes `HmacSha256` as an uninstantiated abstract structure** (`mac_length = 32` only; PR Trust table: *"1. The supplied H is HMAC-SHA256 (FIPS 198-1 over FIPS 180-4): Prose only... Not covered here: bit-level correctness of SHA-256 or HMAC"*). Direct live demand evidence for verified Lean HMAC+HKDF | `Apache-2.0` / Signal orbit; merged `2026-10-26` |
| **`paulbutcher/leancrypto`** | `https://github.com/paulbutcher/leancrypto` (`be0a1d2fa4`, read `README.md`, `LeanCrypto/Hash/SHA2.lean`, `HMAC.lean`) | Pure-Lean SHA-2, HMAC, PKCS#1 RSA | Explicitly unproved hash/MAC (`README.md`: SHA-2 and HMAC *"Checked against published vectors, not proved"*) | `Apache-2.0`; Oct 2026 |
| **`SentinelOps-CI/lean-toolchain`** | `https://github.com/SentinelOps-CI/lean-toolchain` (`83616b2439`, read `SentinelOps/SHA256.lean`, `HMAC.lean`) | Pure-Lean SHA-256 and HMAC-SHA-256 | Proves only output-length (`= 32`) and determinism/self-equality (`hmacSha256_verification_correct`); explicitly states FIPS functional correctness is not formalized | `MIT`; 2026 |
| **`proofbundle/lean-{sha-256,hmac-sha-256,hkdf-sha-256}`** | `https://github.com/proofbundle/lean-hmac-sha-256` (+ `-sha-256`, `-hkdf-sha-256`, read repo trees & `README.md`, `2026-09-24`) | Placeholder repository shells | **Empty `"SCAFFOLDED"` / `"NOT_IMPLEMENTED"` stubs** — zero Lean proof or implementation files | `MIT` / `Apache-2.0` stubs; `2026-09-24` |
| **`powdr-labs/eip8200-challenges`** | `https://github.com/powdr-labs/eip8200-challenges` (`c165c97688`, read `Challenge/Sha256/Reference.lean` & `README.md`) | Verification challenge proving EVM bytecode precompile implements `Challenge.Sha256.Reference` | Uses `Reference.lean` as a trusted byte/word spec for bytecode equivalence; not a two-level FIPS bit-spec library | `MIT`; 2026 |
| **`Plonky3/Plonky3-lean`** | `https://github.com/Plonky3/Plonky3-lean` (`ba6bc17883`, read `Plonky3Lean/Spec/Sha256.lean` & `Air/Sha256/*`) | Soundness & completeness of Plonky3 SHA-256 AIR constraints against `Plonky3Lean/Spec/Sha256.lean` | ZK AIR constraint verification of compression step; not an executable `ByteArray` hash + padding formalization | `MIT OR Apache-2.0`; Oct 2026 |
| **`reilabs/freigen`** (+ `eKisNonos/sha256-gf2-r1cs`, `thryec/zkgolf`) | `https://github.com/reilabs/freigen` (`324935e51e`, `Freigen/Circuit/Examples/Sha256.lean`) & `http://eprint.iacr.asia/2026/2141.pdf` | GF(2) / Boolean circuit arithmetization of SHA-256 compression (7,144-bit witness) | Proves circuit gate equivalence for compression only; no FIPS padding/message-digest implementation | `Apache-2.0`; 2026 |
| **`starius/btc-verified`** | `https://github.com/starius/btc-verified` (`6c1813172d`, read `Btc/Sha256.lean`) | Reducible `sha256` and `sha256d` for Bitcoin block-header verification | Implementation-as-spec (`rfl`/test-vector level only) | `MIT`; 2026 |
| **`leanprover/LNSym`** | `https://github.com/leanprover/LNSym` (`5c05220ff9`, searched full repo file tree via GitHub Trees API) | ARMv8 symbolic simulator & machine-code verification | Verified **SHA-512** ARMv8 assembly (`Proofs/SHA512/`); **zero SHA-256 files exist in repo** | `Apache-2.0`; active |
| **`spitters/CatCrypt-core`** | `https://github.com/spitters/CatCrypt-core` (`0b15ddf29d`, read repo tree + `http://eprint.iacr.asia/2026/604.pdf`) | Game-based computational protocol security proofs (HPKE, EDHOC, SPQR) using SSProve-style Lean + hax/libcrux | Treats SHA-256 / HKDF-SHA-256 as computational PRF/RO assumptions or hax-extracted interfaces; does not formalize FIPS 180-4 | `Apache-2.0`; 2026 |
| **Lean 4 core, `Batteries`, `Mathlib4`** | Searched `leanprover/lean4`, `leanprover-community/batteries`, `leanprover-community/mathlib4` via GitHub code search (`sha256`) | Standard libraries | **Confirmed negative:** zero SHA-256 / FIPS 180-4 / FIPS 198-1 definitions exist in core, Batteries, or Mathlib4 | `Apache-2.0` |

#### B. Non-Lean Proof Assistants & Cryptographic Verification Tools

| System | Canonical Artifact | URL & What Was Read | Scope & Architecture | Status |
|---|---|---|---|---|
| **Coq (VST + CompCert + FCF)** | Appel (TOPLAS 2015) & Beringer, Petcher, Ye, Appel (USENIX Security 2015) | `https://github.com/PrincetonUniversity/VST/tree/master/sha` (inspected directory listing: `HMAC256_spec_pad.v`, `HMAC256_spec_concat.v`, `HMAC256_equivalence.v`, `HMAC256_functional_prog.v`, `HMAC256_isPRF.v`) + Appel paper | Full two-level FIPS 180-4 spec + OpenSSL C streaming `SHA256_Init/Update/Final` + **three-layer HMAC-SHA-256** (concatenated FIPS 198-1 spec ↔ padded NMAC/midstate spec ↔ OpenSSL C `HMAC` with key-midstate reuse) + FCF PRF reduction | Complete gold-standard benchmark (C via VST, ~9k LoC SHA-256 + ~9k LoC HMAC) |
| **F\* / Low\* / Vale (HACL\* / EverCrypt / libcrux)** | Zinzindohoué et al. (CCS 2017); `hacl-star` & `libcrux` | `https://github.com/hacl-star/hacl-star/tree/main/specs` (inspected `Spec.SHA2.fst`, `Spec.Agile.HMAC.fst`, `Spec.Agile.HKDF.fst`) | Pure agile F\* specs for SHA-2 (224–512), HMAC, and HKDF (`Extract`+`Expand`), refined to memory-safe/secret-independent Low\* C and Vale assembly (streaming + SIMD); deployed in Firefox, Linux, Python `hashlib` | Complete & deployed at scale |
| **Cryptol + SAW (AWS-LC)** | Dodds et al. / Boston et al. (CAV 2021); `aws-lc-verification` | `https://github.com/awslabs/aws-lc-verification/tree/main/SAW/proof` (inspected `SHA256/SHA256.saw`, `HMAC/verify-HMAC.saw`, `KDF/`) | Bit-accurate Cryptol specs of FIPS 180-4 SHA-256, FIPS 198-1 HMAC, and KDFs checked via symbolic execution + SMT against BoringSSL/AWS-LC C + x86-64/AVX2/SHANI assembly | Complete (SMT/SAW equivalence, non-foundational kernel) |
| **Isabelle/HOL (AFP)** | Aubin Whitley, *Cryptographic Standards in HOL* (`Crypto_Standards`, Feb 2026) | `https://www.isa-afp.org/browser_info/current/AFP/Crypto_Standards/FIPS180_4.html` and `.../FIPS198_1.html` (read AFP theory index & outline PDF) | Literate HOL specifications of **FIPS 180-4** (SHA-1 and full SHA-2 family) and **FIPS 198-1** (HMAC) with separate `FIPS180_4_Test_Vectors` and `FIPS198_1_Test_Vectors` theories. Pure specification + test vectors rather than verified fast machine-word code (whether any separate fast-code refinement exists in AFP outside `Crypto_Standards` was searched via `site:isa-afp.org` with none found; absence of unpublished Isabelle repos is `UNVERIFIED`) | Complete spec + test vectors in AFP |
| **HOL4** | `HOL/examples/Crypto/SHA-2` | `https://github.com/HOL-Theorem-Prover/HOL/tree/master/examples/Crypto/SHA-2` (`sha2Script.sml` directory listing) | Functional HOL4 specification of SHA-256 | Spec-level example |
| **ACL2** | Kestrel Institute `books/kestrel/crypto` | `https://github.com/acl2/acl2/tree/master/books/kestrel/crypto` (inspected `sha-2/`, `hmac/`, `kdf/`, `padding/`) | Executable ACL2 specifications and refinement libraries for SHA-2, HMAC, and KDFs (used in R1CS/ZK verification) | Complete executable spec + refinements |

---

### 1.6 Final Verdict on the Standing Claim

> **Standing claim under test:** *"LeanSha256 is implementation-as-spec AND the two-level spec+equivalence artifact is open [in Lean]."*

- **Conjunct 1 — *"LeanSha256 is implementation-as-spec"*:** **`CONFIRMED`**.
  - *Evidence:* Direct inspection of `packages/LeanSha256/LeanSha256/Core.lean` (`etheorem/etheorem @ 3d56ad2525`) confirms there is only one SHA-256 definition (`LeanSha256.hash`), written directly over `UInt32` and `ByteArray`, accompanied by 17 single-layer structural/size lemmas and the explicit authorial disclaimer at lines 339–344 (*"These don't claim 'computes SHA-256'. That's an empirical claim the NIST asserts settle."*), with NIST CAVP vectors checked via `native_decide` (`Lean.ofReduceBool`) in `LeanSha256Tests/Nist.lean`.
- **Conjunct 2 — *"the two-level spec+equivalence artifact is open"*:** **`REFUTED`**.
  - *Evidence:* Both `remix7531/fips-180-4-lean` (`0018b08f34`, proving `compress_correct`, `sha256_correct`, and `sha224_correct` between a literate bit-level FIPS 180-4 `spec/` and a 64-way unrolled ring-buffer `UInt32` `impl/` under `[propext, Classical.choice, Quot.sound]`) and `pure-algebra/lean4-hash` (`ab7eda433f`, MIT, zero-dependency, proving `sha256_spec`, `sha224_spec`, and streaming `Context.finalize_absorbs` under `[propext, Quot.sound]`, rechecked with `leanchecker --fresh`) establish the two-level pure-Lean artifact at the programme's kernel bar. Closing ticket `#17` was completely justified.

---

## 2. Spec Architecture (Evaluating Candidates & Designing the Best Open Target)

### 2.1 Candidate-by-Candidate Elimination Against the Primary-Source Sweep

Before designing an architecture, every candidate named in `BRIEF.md` (plus `HKDF-SHA-256`) must be tested against what actually exists on GitHub as of `2026-10-27`:

| Candidate Target | Verdict After Sweep | Exact Technical / Evidentiary Reason |
|---|---|---|
| **1. SHA-224 two-level formalization** | **TAKEN (×2 pure-Lean + ×1 Rust/Aeneas)** | Proved at the kernel bar in `remix7531/fips-180-4-lean` (`SHS.Equiv.SHA256.sha224_correct`, `[propext, Classical.choice, Quot.sound]`), in `pure-algebra/lean4-hash` (`Hash.Sha256.sha224_spec`, `[propext, Quot.sound]`), and for Rust in `remix7531/hashes-fv` (`sha224_spec`). Opening a SHA-224 lane would duplicate existing work. |
| **2. Maintained standalone SHA-256 spec+impl library** | **TAKEN** (modulo `< 2^64` domain guard) | `pure-algebra/lean4-hash` (`MIT`, zero external dependencies, Lean `v4.33.1`, `leanchecker --fresh` in CI) already provides an importable standalone `Spec` + `Impl` + `Fast` library, avoiding `fips-180-4-lean`'s `GPL-3.0-or-later` and Mathlib hurdles. Its sole specification blemish is omitting the `M.length < 2^64` domain guard in `Spec.pad`. |
| **3. Streaming `init`/`update`/`final` SHA-256 proved equivalent to one-shot spec** | **TAKEN for raw SHA-256** | `pure-algebra/lean4-hash/Hash/Sha256/Context.lean` already defines `Context.init`, `Context.update`, and `Context.finalize` (`buffer.size < 64`) and proves chunk-invariance (`update_append`) and one-shot spec equivalence (`finalize_absorbs` + `Bridge.sha256_bridge`) under `[propext, Quot.sound]`. |
| **4. Discharging SizzLean's three `*_eq_spec` FFI-bridge axioms with real theorems** | **LOGICALLY IMPOSSIBLE AS STATED** (only a pure-Lean `@[csimp]` variant is possible) | Primary source `packages/hazmat/LeanHazmatSha256/LeanHazmatSha256/Ffi.lean` (`etheorem/etheorem @ 3d56ad2525`) declares `sha256Hash`, `sha256Combine`, and `sha256BatchCombine` as `@[extern "lean_hazmat_..."] opaque ... : ByteArray`. In Lean 4's kernel, an `opaque` constant has **no definitional body** — only non-emptiness of its return type (`Inhabited ByteArray`). Consequently, `LeanHazmatSha256.sha256Hash = LeanSha256.hash` is **logically independent** of `[propext, Classical.choice, Quot.sound]` and **cannot** be proved as a kernel theorem while `sha256Hash` binds to OpenSSL C FFI. What `Sha256Equiv.lean` docstrings allude to via `@[csimp]` is replacing the C FFI call with a *pure-Lean* fast `UInt32` implementation `fastHash` proved equal to `LeanSha256.hash` (`@[csimp] theorem hash_eq_fastHash : @LeanSha256.hash = @fastHash`), which gives ~170 MiB/s pure-Lean runtime substitution without axioms, **or** proving `LeanSha256.hash` equal to a FIPS 180-4 bit-spec — neither of which verifies OpenSSL C/SHA-NI or Intel ISA-L AVX2 multi-buffer SIMD. |
| **5. Two-level pure-Lean `HMAC-SHA-256` (FIPS 198-1) + `HKDF-SHA-256` (RFC 5869) over a FIPS 180-4 spec, with NMAC key-midstate precomputation & streaming HMAC** | **GENUINELY OPEN & SELECTED TARGET** | **Every** standalone Lean 4 HMAC package (`kim-em/lean-crypto-hash`, `paulbutcher/leancrypto`, `SentinelOps-CI/lean-toolchain`) is explicitly implementation-as-spec; `proofbundle/lean-{hmac,hkdf}-sha-256` are empty `"NOT_IMPLEMENTED"` scaffolds; `pyca/verified-garbage` leaves long-key HMAC (`|K| > 64`) in unverified Rust and has no HKDF; `thevilledev/ocaml-pq` has only a `noncomputable` (`Classical.choose`) OCaml list model coupled to Mathlib with no executable `ByteArray` code, no midstate/streaming HMAC, and no HKDF; and **`Beneficial-AI-Foundation/libsignal-verify` PR #43 (merged `2026-10-26`) explicitly axiomatized `HmacSha256` as an unproved abstract structure** for Signal's PQXDH key schedule. |

**Selected Target:** **A zero-dependency, MIT/Apache-2.0 standalone Lean 4 formalization of `HMAC-SHA-256` (FIPS 198-1 / RFC 2104) and `HKDF-SHA-256` (RFC 5869), proved equivalent at the kernel bar to an independently readable, domain-exact (`< 2^64`-bit) FIPS 180-4 SHA-256 specification — covering one-shot, precomputed NMAC key-midstate (`KeySchedule`), and incremental streaming (`HmacContext.init`/`update`/`finalize`) implementations, plus thin adapter lemmas instantiating `libsignal-verify`'s `HmacSha256` interface and bridging `LeanSha256.hash`.**

> **Architectural decision — self-contained FIPS 180-4 foundation vs importing `pure-algebra/lean4-hash`:**
> The package should include its own concise (~200-line), domain-exact (`M.length < 2 ^ 64`) FIPS 180-4 bit/word specification and ~250-line unrolled `UInt32` block compressor (with an optional 30-line bridge file proving equality with `pure-algebra/lean4-hash`'s `Hash.Sha256.Spec.sha256_bytes` on `msg.size < 2 ^ 61` and `LeanSha256.hash`). Two technical facts force this choice:
> 1. **Domain-bound soundness for HMAC:** HMAC prepends a 64-byte (`512`-bit) key pad `K₀ ⊕ ipad` before `text`, so FIPS 180-4's `< 2^64`-bit bound translates to `text.size < 2 ^ 61 - 64` bytes (`8 * (64 + text.size) < 2 ^ 64`). Because `pure-algebra/lean4-hash`'s `Spec.pad` omits the `< 2^64` precondition and wraps lengths modulo `2^64`, importing its `Spec` alone would fail to catch length-overflow bugs on `[2^61 - 64, 2^61)`.
> 2. **Midstate-exposure requirement:** Precomputed HMAC (`KeySchedule`) and outer-digest single-block compression operate directly on intermediate 8-word chaining states `Vector UInt32 8` (`compress state block`) and `absorbedBlocks := 1`, which require white-box access to the Merkle-Damgård block-step lemmas rather than a black-box `ByteArray → Digest 32` API.

---

### 2.2 Abstract Specification Layer (`Spec/`)

The abstract layer is written strictly as a human-auditable transcription of the three NIST/IETF standards, with zero performance compromises (`UInt32`, ring buffers, mutability, and `ByteArray` offsets are completely excluded from `Spec/`).

#### Layer S0: FIPS 180-4 SHA-256 (`Spec/Fips180_4.lean`)
- **Words, bits, and rotations (§3.1–3.2):**
  - `abbrev BitString := List Bool` (most-significant-bit-first within both bytes and 32-bit words, per FIPS 180-4 §3.1).
  - `abbrev Word := BitVec 32`, `abbrev Block := Vector Word 16`, `abbrev Schedule := Vector Word 64`, `abbrev State := Vector Word 8`.
  - Round functions (§4.1.2) directly over `BitVec 32`:
    ```lean
    def Ch   (x y z : Word) : Word := (x &&& y) ^^^ (~~~x &&& z)
    def Maj  (x y z : Word) : Word := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
    def Σ0   (x : Word)     : Word := x.rotateRight 2  ^^^ x.rotateRight 13 ^^^ x.rotateRight 22
    def Σ1   (x : Word)     : Word := x.rotateRight 6  ^^^ x.rotateRight 11 ^^^ x.rotateRight 25
    def σ0   (x : Word)     : Word := x.rotateRight 7  ^^^ x.rotateRight 18 ^^^ (x >>> 3)
    def σ1   (x : Word)     : Word := x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ (x >>> 10)
    ```
  - Constants `K : Vector Word 64` (§4.2.2) and initial chaining state `H0 : State` (§5.3.3).
- **Schedule & compression (§6.2.2) as pure functional recurrences:**
  - `schedule (M : Block) : Schedule` constructed via `Vector.ofFn` / bounded recursion: `W[t] = M[t]` for `0 ≤ t < 16`, and `W[t] = σ1 W[t-2] + W[t-7] + σ0 W[t-15] + W[t-16]` for `16 ≤ t < 64`.
  - `roundStep (W : Schedule) (t : Fin 64) (s : State) : State` updating the 8-tuple `#v[T1 + T2, a, b, c, d + T1, e, f, g]`, and `compress (H : State) (M : Block) : State := Vector.zipWith (· + ·) H (Fin.foldl 64 (fun s t => roundStep (schedule M) t s) H)`.
- **Padding as a proved construction (§5.1.1 & §5.2.1):**
  - Define `padZeroCount (ℓ : Nat) : Nat := (959 - ℓ % 512) % 512` and prove its characterizing specification theorem (rather than leaving modular arithmetic implicit):
    1. `padZeroCount_lt (ℓ : Nat) : padZeroCount ℓ < 512`
    2. `padZeroCount_mod (ℓ : Nat) : (ℓ + 1 + padZeroCount ℓ) % 512 = 448`
    3. `padZeroCount_minimal (ℓ k : Nat) : k < 512 → (ℓ + 1 + k) % 512 = 448 → k = padZeroCount ℓ`
  - Define domain-guarded `pad (M : BitString) (h : M.length < 2 ^ 64) : { P : BitString // P.length % 512 = 0 ∧ 512 ≤ P.length }` appending `true :: List.replicate (padZeroCount M.length) false ++ bitsOfUInt64BE M.length`.
  - Prove **padding injectivity** (`pad_injective : ∀ M₁ M₂ h₁ h₂, (pad M₁ h₁).val = (pad M₂ h₂).val → M₁ = M₂`) by reading `M.length` back out of the trailing 64 bits (`natOfBits_bitsOfUInt64BE` under `h : M.length < 2 ^ 64`) and slicing `take M.length` — directly exposing why the `< 2^64` guard is mathematically load-bearing.
  - Define `parse : { P : BitString // P.length % 512 = 0 } → List Block`, `sha256Bits (M : BitString) (h : M.length < 2 ^ 64) : BitVec 256`, and byte-level `sha256Bytes (msg : List UInt8) (h : msg.length < 2 ^ 61) : List UInt8` (with `sha256Bytes_length : (sha256Bytes msg h).length = 32`).

#### Layer S1: FIPS 198-1 HMAC-SHA-256 (`Spec/Fips198_1.lean`)
Transcribed directly from NIST FIPS 198-1 §4 ("HMAC Specification", Table 1 parameters `B = 64`, `L = 32`):
- `def ipadByte : UInt8 := 0x36` and `def opadByte : UInt8 := 0x5c`.
- **Step 1–3 (`keyToBlock`):**
  ```lean
  def keyToBlock (K : List UInt8) (hK : K.length < 2 ^ 61) : List UInt8 :=
    if h : K.length ≤ 64 then
      K ++ List.replicate (64 - K.length) 0x00
    else
      let kd := sha256Bytes K hK
      kd ++ List.replicate 32 0x00
  ```
  accompanied by `theorem keyToBlock_length (K hK) : (keyToBlock K hK).length = 64`.
- **Step 4–9 (`hmacSha256Spec`):**
  ```lean
  def xorPad (padByte : UInt8) (K0 : List UInt8) : List UInt8 :=
    K0.map (· ^^^ padByte)

  def hmacSha256Spec (K text : List UInt8)
      (hK : K.length < 2 ^ 61) (hText : text.length < 2 ^ 61 - 64) : List UInt8 :=
    let K0 := keyToBlock K hK
    let innerInput := xorPad ipadByte K0 ++ text
    have hInner : innerInput.length < 2 ^ 61 := by ... -- 64 + text.length < 2^61
    let innerDigest := sha256Bytes innerInput hInner
    let outerInput := xorPad opadByte K0 ++ innerDigest
    have hOuter : outerInput.length < 2 ^ 61 := by ... -- 64 + 32 = 96 < 2^61
    sha256Bytes outerInput hOuter
  ```
  Notice there is **zero** mention of midstates, ring buffers, or fixed-96-byte outer padding templates in `Spec/Fips198_1.lean`: it is literally `H((K₀ ⊕ opad) ‖ H((K₀ ⊕ ipad) ‖ text))`.

#### Layer S2: RFC 5869 HKDF-SHA-256 (`Spec/Rfc5869.lean`)
Transcribed directly from IETF RFC 5869 §2.2 (`HKDF-Extract`) and §2.3 (`HKDF-Expand`) with `HashLen = 32`:
- **`hkdfExtractSpec (salt? : Option (List UInt8)) (ikm : List UInt8)`** (for `(salt?.getD (List.replicate 32 0)).length < 2 ^ 61` and `ikm.length < 2 ^ 61 - 64`):
  ```lean
  def hkdfExtractSpec (salt? : Option (List UInt8)) (ikm : List UInt8)
      (hSalt : (salt?.getD (List.replicate 32 0)).length < 2 ^ 61)
      (hIkm : ikm.length < 2 ^ 61 - 64) : List UInt8 :=
    hmacSha256Spec (salt?.getD (List.replicate 32 0)) ikm hSalt hIkm
  ```
- **`hkdfExpandSpec (prk info : List UInt8) (L : Nat)`** (with `hL : L ≤ 255 * 32`, `hPrk : prk.length < 2 ^ 61` — note RFC 5869 §2.3 permits general `prk` of `≥ HashLen` octets — and `hInfo : info.length < 2 ^ 61 - 97`, ensuring `|T(i-1)| + |info| + 1 ≤ 32 + info.length + 1 < 2 ^ 61 - 64`):
  ```lean
  def hkdfBlockSpec (prk info : List UInt8) (hPrk : prk.length < 2 ^ 61)
      (hInfo : info.length < 2 ^ 61 - 97) : Nat → List UInt8
    | 0     => []
    | i + 1 =>
        let prev := hkdfBlockSpec prk info hPrk hInfo i
        hmacSha256Spec prk (prev ++ info ++ [UInt8.ofNat (i + 1)]) hPrk (by ...)

  def hkdfExpandSpec (prk info : List UInt8) (L : Nat)
      (hL : L ≤ 255 * 32) (hPrk : prk.length < 2 ^ 61)
      (hInfo : info.length < 2 ^ 61 - 97) : List UInt8 :=
    let n := (L + 31) / 32
    ((List.range n).flatMap (fun idx => hkdfBlockSpec prk info hPrk hInfo (idx + 1))).take L
  ```

---

### 2.3 Executable Implementation Layer (`Impl/`)

The executable layer is engineered for real pure-Lean throughput and ergonomic cryptographic APIs — intentionally diverging structurally from `Spec/` so the equivalence proof does nontrivial work:

1. **Fast `UInt32` SHA-256 Core (`Impl/Sha256Fast.lean`):**
   - Unboxed `State8` structure of eight `UInt32` fields (`h0 .. h7 : UInt32`), 4-byte big-endian loads directly from `ByteArray` at `offset : Nat` (`loadU32BE`), and a 64-round compile-time unrolled compression step (`compressBlockAt : State8 → ByteArray → (offset : Nat) → (h : offset + 64 ≤ data.size) → State8`) using a 16-word `UInt32` schedule ring buffer updated mod 16.
   - Streaming `Sha256Context` (`init`, `update`, `finalize`) + one-shot `sha256 (data : ByteArray) : ByteArray`.
2. **Precomputed NMAC Key Schedule (`Impl/HmacKeySchedule.lean`):**
   - `structure HmacKeySchedule where innerState : State8; outerState : State8`.
   - `HmacKeySchedule.ofKey (key : ByteArray) : HmacKeySchedule`:
     - Normalizes `key` in a single 64-byte buffer `k0` (if `key.size ≤ 64`, copies `key` + zero fill; if `key.size > 64`, calls `Impl.sha256 key` + 32 zero bytes).
     - Forms the two 64-byte XOR blocks `k0 ^^^ 0x36` and `k0 ^^^ 0x5c` and compresses each **once** from `State8.iv256` to produce `innerState` and `outerState`. (Zero raw key bytes need be retained in `HmacKeySchedule`!)
3. **Streaming & One-Shot HMAC (`Impl/Hmac.lean`):**
   - `structure HmacContext where ks : HmacKeySchedule; state : State8; buf : ByteArray; buf_lt : buf.size < 64; msgBytes : UInt64`.
   - `HmacContext.init (ks : HmacKeySchedule) : HmacContext` sets `state := ks.innerState`, `buf := ByteArray.empty`, `msgBytes := 0`.
   - `HmacContext.update (ctx : HmacContext) (chunk : ByteArray) : HmacContext` drains complete 64-byte blocks directly from `chunk` without copying the middle blocks through `buf`, keeping only `< 64` trailing bytes in `buf` and adding `chunk.size.toUInt64` to `msgBytes`.
   - `HmacContext.finalize (ctx : HmacContext) : ByteArray`:
     1. Finalizes `ctx.state` + `ctx.buf` using **encoded total bit length `(64 + ctx.msgBytes) <<< 3`** (accounting for the pre-compressed 64-byte `K₀ ⊕ ipad` block!) into eight `UInt32` inner digest words `d0 .. d7`.
     2. Executes **one specialized outer block compression** `compressWords16 ctx.ks.outerState #v[d0, d1, d2, d3, d4, d5, d6, d7, 0x80000000, 0, 0, 0, 0, 0, 0, 0x00000300]` (`768 = 0x300` bits = 64-byte `K₀ ⊕ opad` + 32-byte `innerDigest`) and serializes the resulting `State8` to a 32-byte `ByteArray` — **zero `ByteArray` allocations for the outer hash!**
   - One-shot `hmacSha256 (key msg : ByteArray) : ByteArray := (HmacContext.init (HmacKeySchedule.ofKey key) |>.update msg).finalize`.
4. **Midstate-Reusing HKDF (`Impl/Hkdf.lean`):**
   - `hkdfExtract (salt? : Option ByteArray) (ikm : ByteArray) : ByteArray`.
   - `hkdfExpand (prk info : ByteArray) (L : Nat) (hL : L ≤ 255 * 32) : ByteArray`: builds `ks := HmacKeySchedule.ofKey prk` **once**, loops `i` from `1` to `(L + 31) / 32`, feeds `prev` (`0` bytes on `i = 1`, `32` bytes on `i > 1`), `info`, and `[UInt8.ofNat i]` into `HmacContext.init ks`, appends `min 32 (L - written)` bytes to an output `ByteArray`, and returns an exact `L`-byte `ByteArray`.

---

### 2.4 Equivalence-Proof Plan (`Equiv/` — Bridge Lemmas & Hard Steps)

 mirroring Appel/Beringer's Coq decomposition (`HMAC256_spec_concat` ↔ `HMAC256_spec_pad` ↔ `HMAC256_functional_prog`), the proof factors into five clean bridges so no single proof mixes bit-level algebra with `ByteArray` index arithmetic:

```
Impl.hmacSha256 / HmacContext.finalize
   │  (Bridge B4: streaming buffer/slice invariant + B1: UInt32 ring-buffer ↔ BitVec 32)
   ▼
MidstateRef.hmacMidstate (pure List UInt8 / State, precomputed H_in & fixed 16-word outer block)
   │  (Bridge B2: 1-block Merkle-Damgård prefix split + B3: 96-byte outer pad template)
   ▼
Spec.hmacSha256Spec (FIPS 198-1 concatenated byte/bit spec over Spec.sha256Bytes)
```

1. **Bridge B1 — Word, Schedule Ring-Buffer, and Compression Equivalence (`Equiv/CompressBridge.lean`):**
   - `loadU32BE_toBitVec`: 4-byte `UInt8` big-endian assembly equals `Word.ofBits (bitsOfBytes (bs.slice off (off+4)))`.
   - `ringBuffer_step_invariant`: after round `t < 64`, slot `(t + j) % 16` (`0 ≤ j < 16`) of the mutable 16-word `UInt32` ring buffer equals `(Spec.schedule M)[t + j]` (for `t + j < 64`). Unrolling `unroll64` reduces by bounded induction over `Fin 64` (`simp` using `Init`'s `rfl` lemmas `UInt32.toBitVec_and/or/xor/not/shiftLeft/shiftRight/add` and `BitVec.rotateRight_def` — **never** `bv_decide`, which pulls in `Lean.ofReduceBool`!).
   - Deliverable lemma: `toSpecState (Impl.compressBlockAt s bs off h) = Spec.compress (toSpecState s) (parseBlockBytes (bs.extract off (off + 64)))`.
2. **Bridge B2 — Merkle-Damgård 1-Block Prefix Splitting & Length Shift (`Equiv/PrefixSplit.lean`) [HARD STEP #1]:**
   - *Why it is hard:* In `Spec.sha256Bytes (B₆₄ ++ M)`, `pad` operates on the *entire* concatenated bit string `bitsOfBytes B₆₄ ++ bitsOfBytes M` of length `512 + 8 * M.length`. One must prove that `parse (pad (bitsOfBytes B₆₄ ++ bitsOfBytes M) h)` equals `[parseBlockBytes B₆₄] ++ parse (padWithShiftedLen (bitsOfBytes M) (512 + 8 * M.length) h)`.
   - *Key sub-lemmas:*
     - `padZeroCount_add_512 (ℓ : Nat) : padZeroCount (512 + ℓ) = padZeroCount ℓ` (`omega` on `(959 - (512 + ℓ) % 512) % 512`).
     - `parse_append_512 (P₁ P₂ : BitString) (h₁ : P₁.length = 512) (h₂ : P₂.length % 512 = 0) : parse (P₁ ++ P₂) = blockOf512Bits P₁ :: parse P₂`.
     - `foldl_compress_cons`: folding `Spec.compress` from `H0` over `(B₀ :: Bs)` equals folding `Spec.compress` from `Spec.compress H0 B₀` (= `innerState`) over `Bs`!
     - Length-bound transfer: `M.length < 2 ^ 61 - 64 → 8 * (64 + M.length) < 2 ^ 64`, proving `UInt64` bit-length calculation `(64 + ctx.msgBytes) <<< 3` never wraps modulo `2^64`.
3. **Bridge B3 — Fixed-Template Outer Compression (`Equiv/OuterBlockBridge.lean`):**
   - Prove that for *any* 64-byte block `opadBlock` (`K₀ ⊕ opad`) and *any* 32-byte `innerDigest`, `parse (pad (bitsOfBytes (opadBlock ++ innerDigest)) (by decide))` has **exact length 2 blocks**: block 0 is `parseBlockBytes opadBlock`, and block 1 is `#v[d₀, …, d₇, 0x80000000, 0, 0, 0, 0, 0, 0, 0x00000300]` (`padZeroCount 768 = (959 - 256) % 512 = 192` zero bits = `31` bits after `1` plus five 32-bit zero words, followed by `bitsOfUInt64BE 768 = [0x00000000, 0x00000300]`).
   - This discharges the zero-allocation `compressWords16` optimization in `HmacContext.finalize` in ~50 lines of clean bit/word algebra.
4. **Bridge B4 — Streaming `HmacContext` Chunk-Split Invariance (`Equiv/StreamingHmacBridge.lean`) [HARD STEP #2]:**
   - *Why it is hard:* `HmacContext.update` has three control-flow regimes (`buf.size + chunk.size < 64`, `buf.size = 0 ∧ chunk.size ≥ 64` fast-path zero-copy loop, and `buf.size > 0 ∧ buf.size + chunk.size ≥ 64` fill-buffer-then-loop), involving fiddly `ByteArray.extract` / `List.take` / `List.drop` indexing.
   - *Solution:* Define relational invariant `HmacAbsorbs (ks : HmacKeySchedule) (ctx : HmacContext) (acc : List UInt8) : Prop` asserting: (i) `ctx.ks = ks`, (ii) `acc.length < 2 ^ 61 - 64 → ctx.msgBytes.toNat = acc.length`, (iii) `ctx.buf.data.toList = acc.drop (64 * (acc.length / 64))`, and (iv) `toSpecState ctx.state = (blocksOf64 (acc.take (64 * (acc.length / 64)))).foldl Spec.compress (toSpecState ks.innerState)`. Prove `absorbs_init`, `absorbs_update` (establishing `update_append : (ctx.update a).update b = ctx.update (a ++ b)` as an immediate corollary), and `finalize_absorbs_eq_fips198`.
5. **Bridge B5 — Key Normalization & RFC 5869 `hkdfExpand` Induction (`Equiv/HkdfBridge.lean`):**
   - Case-split on `key.size ≤ 64` vs `64 < key.size < 2 ^ 61`, using SHA-256's one-shot theorem on the long-key branch to prove `HmacKeySchedule.ofKey` produces `Spec.compress H0 (parseBlockBytes (Spec.keyToBlock key.toList hK))` for both `ipad` and `opad`.
   - Induct over `idx < n = (L + 31) / 32` (`n ≤ 255`) for `hkdfExpand`: because `1 ≤ idx + 1 ≤ 255 < 256`, `UInt8.ofNat (idx + 1)` preserves counter distinctness, and slicing `take L` matches `Spec.hkdfExpandSpec`.
   - Headline theorems (`Equiv/Main.lean`, all gated by `#guard_msgs in #print axioms` + `leanchecker --fresh`):
     - `hmacSha256_eq_spec (key msg : ByteArray) (hK : key.size < 2 ^ 61) (hM : msg.size < 2 ^ 61 - 64) : (Impl.hmacSha256 key msg).toList = Spec.hmacSha256Spec key.toList msg.toList hK hM`
     - `hmacContext_stream_eq_spec` (arbitrary list of `ByteArray` chunks folded via `HmacContext.update` equals `Spec.hmacSha256Spec` of their concatenation)
     - `hkdfExtract_eq_spec` & `hkdfExpand_eq_spec` & `hkdf_eq_spec` (end-to-end RFC 5869 equivalence).

---

### 2.5 Test-Vector Sources & Kernel-Checkable Integration WITHOUT `native_decide`

#### Authoritative Vector Sources (Vendored with SHA-256 Manifests)
1. **NIST CAVP Secure Hash Standard (`SHA256ShortMsg.rsp`, `SHA256LongMsg.rsp`, CAVS 11.0) & FIPS 180-4 §B:**
   - Anchor boundary lengths: `0` bytes (`Len = 0` — taking care of CAVP's notorious `Msg = 00` placeholder trap where `Len = 0` means `[]`, *not* `[0x00]`), `3` bytes (`"abc"`, non-symmetric endian witness), `55` bytes (`440` bits, maximum 1-block message), `56` bytes (`448` bits, minimum 2-block spill), and `64` bytes (`512` bits, exact block boundary forcing an all-padding second block).
2. **IETF RFC 4231 (§4.1–4.7, Test Cases 1–7) + NIST CAVP `HMAC.rsp` (`[L=32]` section):**
   - RFC 4231 Cases 1–4 (`20`-byte and `25`-byte keys, `8`–`50`-byte messages), Case 5 (`128`-bit truncation check), **Case 6** (`131`-byte `0xaa` key `> 64` bytes, exercising the `key.size > B` SHA-256 pre-hashing branch + `54`-byte message), and **Case 7** (`131`-byte `0xaa` key + `152`-byte multi-block message, exercising both key pre-hashing and multi-block inner streaming).
3. **IETF RFC 5869 Appendix A (§A.1–A.3, SHA-256 Test Cases 1–3):**
   - **Test Case 1:** `22`-byte IKM, `13`-byte salt, `10`-byte info, `L = 42` (`2` expand blocks, partial final block truncation).
   - **Test Case 2:** `80`-byte IKM (`> 64`), `80`-byte salt (`> 64`, exercising long-key HMAC inside `HKDF-Extract`!), `80`-byte info (`> 64`, exercising multi-block inner HMAC inside `HKDF-Expand`!), `L = 82` (`3` expand blocks).
   - **Test Case 3:** `22`-byte IKM, **empty salt (`none` / `0` octets → defaults to `32` zero bytes)**, **empty info (`[]`)**, `L = 42`.

#### How to Check Vectors at the Kernel Bar WITHOUT `native_decide` Trust

Inspecting how existing Lean 4 repos handle vectors reveals four distinct mechanisms with sharply different trust footprints:

| Mechanism | Compiler / VM in Trust Base? | Emits Kernel Theorem? | Axioms Added (`#print axioms`) | Behavior on SHA-256 / HMAC / HKDF |
|---|---|---|---|---|
| `by native_decide` *(used in `LeanSha256`)* | **YES** (trusts C/LLVM codegen + FFI) | Yes | **`Lean.ofReduceBool`** (fails strict standard-axiom bar!) | Fast, **disqualified by brief** |
| `#guard (f x == y)` *(used in `lean4-hash` for W2–E3)* | **YES** (elaborator VM check only) | **NO** (invisible to `leanchecker`) | N/A (not a declaration) | Useful auxiliary sanity check, **not kernel evidence** |
| `by decide` / `by rfl` | No | Yes | `[]` (none) | **Fails (`maxRecDepth`)** in `MetaM`'s `whnf` elaborator on 64-round `BitVec 32` SHA-256 |
| **`by decide +kernel` + `rw [← equiv_thm]`** *(proven pattern from `lean4-hash/Hash/Sha256/Kats.lean:218`)* | **NO (100% C++ kernel WHNF + `leanchecker --fresh`)** | **YES** | **`[]` on `Spec`/`List UInt8` KATs; `[propext, Quot.sound]` after `rw` onto `ByteArray` `Impl`** | **Succeeds cleanly** when evaluated on pure `List UInt8` / `BitVec 32` terms and transferred via equivalence! |

**Concrete two-tier verification protocol:**
1. **Tier 1 — Kernel-Checked Anchor Suite (`Tests/KernelKats.lean`, zero `native_decide`, zero compiler trust):**
   - State every anchor vector (`5` SHA-256 boundary vectors, **all `7` RFC 4231 HMAC-SHA-256 vectors** including 131-byte keys and 152-byte multi-block messages, streaming chunk-split witnesses, and **all `3` RFC 5869 HKDF-SHA-256 vectors** for both `PRK` and `OKM`) as genuine `theorem`s:
     - First prove the equality on the pure `List UInt8` / `BitVec 32` byte-reference (`Spec` or `ByteRef`, avoiding opaque `ByteArray` constructors) using **`by decide +kernel`**, which constructs `of_decide_eq_true (Eq.refl true)` checked directly by Lean's kernel reducer (bypassing `MetaM` recursion depth limits and adding **zero** axioms).
     - For multi-call HKDF vectors like RFC 5869 Case A.2 (~10 compression blocks total), factor intermediate kernel reductions per step (`lemma rfc5869_a2_prk_spec : ... := by decide +kernel`, `lemma rfc5869_a2_t1_spec : ... := by decide +kernel`, `t2`, `t3`) so each `decide +kernel` invocation reduces only 2–4 block compressions (~50–150 ms in the kernel).
     - Immediately transfer every anchor theorem onto the fast `ByteArray` public API (`Impl.hmacSha256`, `Impl.hkdf`) by rewriting with `hmacSha256_eq_spec` / `hkdf_eq_spec`! Pin `#guard_msgs in #print axioms` on the resulting `Impl` KAT theorems to verify they depend **only** on `[propext, Quot.sound]` (or `[propext, Classical.choice, Quot.sound]`), with **zero `Lean.ofReduceBool`**.
2. **Tier 2 — Bulk Runtime Regression Runner (`Tests/CavpRunnerMain.lean`, `lean_exe` outside library import closure):**
   - A standalone `IO` executable (kept strictly out of the library and `Verified` target closure, just as `remix7531/fips-180-4-lean/tests/CAVPMain.lean` and `kim-em/lean-crypto-hash` do) that parses the full vendored NIST CAVP `SHA256ShortMsg.rsp`, `SHA256LongMsg.rsp`, `HMAC.rsp`, and Project Wycheproof `hmac_sha256_test.json` + `hkdf_sha256_test.json` (~2,000+ vectors total) in < 1 second at CI time.

---

## 3. Milestone Decomposition

The chosen target decomposes into **six single-lane milestones (`M1`–`M6`)** with a **critical-path depth of 4 stages** (`M1 → {M2 ‖ M3} → M4 → {M5 ‖ M6}`), sized at ~250–550 LoC each so no lane hits context or heartbeat ceilings.

### Universal Kernel-Bar Acceptance Gate (Required of Every Milestone `M1`–`M6`)
Every milestone PR/lane must pass all four checks before merge:
1. **Clean full build:** `lake build` exits `0` with zero warnings on unused variables or linter errors.
2. **Zero escape hatches:** Repository-wide grep confirms **zero** occurrences of `sorry`, `admit`, `axiom`, `opaque`, `@[extern]`, `unsafe`, `partial`, or `native_decide` across `Spec/`, `Impl/`, `Equiv/`, and `Tests/KernelKats.lean`.
3. **Pinned standard-axiom gate:** Every milestone ships or extends an `AxiomCheck` module using `#guard_msgs in #print axioms <theorem>` on every public theorem of that milestone, showing **only a subset of `[propext, Classical.choice, Quot.sound]`** (targeting `[propext, Quot.sound]` on constructive modules and `[]` on direct `decide +kernel` spec KATs).
4. **Fresh kernel replay:** `lake env leanchecker --fresh <MilestoneRootModule>` exits `0`, defeating environment-manipulation or elaborator bugs.

---

### Dependency Graph & Parallelism Plan

```
                    ┌──────────────────────────────────────────┐
                    │ M1: Standards Spec Layer (FIPS 180-4,    │
                    │     FIPS 198-1, RFC 5869) + Spec KATs    │
                    └────────────────────┬─────────────────────┘
                                         │ (Spec frozen)
                      ┌──────────────────┴──────────────────┐
                      ▼ (Parallel Lane A)                   ▼ (Parallel Lane B)
       ┌──────────────────────────────┐      ┌──────────────────────────────────┐
       │ M2: Fast UInt32 SHA-256 Core │      │ M3: NMAC Midstate & 96-Byte      │
       │     & One-Shot Equivalence   │      │     Outer-Template Spec Proofs   │
       └──────────────┬───────────────┘      └─────────────────┬────────────────┘
                      └──────────────────┬─────────────────────┘
                                         ▼
                    ┌──────────────────────────────────────────┐
                    │ M4: Precomputed KeySchedule + Streaming  │
                    │     HmacContext (init/update/finalize)   │
                    │     & FIPS 198-1 Equivalence Theorem     │
                    └────────────────────┬─────────────────────┘
                                         │ (HMAC API + theorems frozen)
                      ┌──────────────────┴──────────────────┐
                      ▼ (Parallel Lane C)                   ▼ (Parallel Lane D)
       ┌──────────────────────────────┐      ┌──────────────────────────────────┐
       │ M5: HKDF-SHA-256 (RFC 5869)  │      │ M6: Bulk CAVP/Wycheproof Runner, │
       │     Impl, Equivalence &      │      │     Ecosystem Bridges & Global   │
       │     Full Kernel KAT Suite    │      │     Declaration Axiom Audit      │
       └──────────────────────────────┘      └──────────────────────────────────┘
```

- **Parallel Pair 1 (`M2 ‖ M3` after `M1`):** `M2` touches only `Impl/Sha256Fast.lean` and `Equiv/CompressBridge.lean` (`UInt32` ring-buffer unrolling and `ByteArray` slicing against `Spec.Fips180_4`), whereas `M3` works **purely over `Spec/` types** (`List Bool`, `List UInt8`, `BitVec 32`) to prove Hard Step #1 (512-bit Merkle-Damgård prefix splitting and 96-byte outer compression template equivalence against `Spec.Fips198_1`). Zero file overlap.
- **Parallel Pair 2 (`M5 ‖ M6` after `M4`):** Once `M4` freezes `Impl.HmacKeySchedule`, `Impl.hmacSha256`, and `hmacSha256_eq_spec`, `M5` builds `HKDF-SHA-256` and the RFC 5869 / RFC 4231 kernel KAT theorems in parallel with `M6`'s bulk `IO` test runner (`CAVP` + Wycheproof) and ecosystem adapter modules.

---

### Per-Milestone Specifications

#### Milestone `M1` — Domain-Exact Standards Transcription & Anchor Spec Sanity (`Spec/`)
- **Dependencies:** None (root milestone).
- **Scope:** Transcribe FIPS 180-4 (`< 2^64` bits), FIPS 198-1 (`HMAC-SHA-256`), and RFC 5869 (`HKDF-SHA-256`) into clean mathematical Lean 4 with zero external dependencies; prove foundational padding/length structural theorems; execute anchor `decide +kernel` sanity checks directly on `Spec` to lock in MSB-first bit/byte conventions before parallel lanes fork.
- **Deliverables:**
  - `lakefile.lean` / `lean-toolchain` (pinned current stable Lean 4, zero external dependencies, MIT/Apache-2.0 license).
  - `Spec/Fips180_4.lean`: `BitString`, `Word` (`BitVec 32`), `Ch`/`Maj`/`Σ0`/`Σ1`/`σ0`/`σ1`, `K`, `H0`, `schedule`, `compress`, domain-guarded `pad`, `parse`, `sha256Bits`, `sha256Bytes`, plus proved `padZeroCount_minimal`, `pad_injective`, and `sha256Bytes_length`.
  - `Spec/Fips198_1.lean`: `keyToBlock`, `keyToBlock_length`, `hmacSha256Spec`, `hmacSha256Spec_length`.
  - `Spec/Rfc5869.lean`: `hkdfExtractSpec`, `hkdfBlockSpec`, `hkdfExpandSpec`, `hkdfExpandSpec_length`.
  - `Tests/SpecSanityKats.lean`: `by decide +kernel` theorems on `Spec` for CAVP `Len = 0`, `"abc"`, RFC 4231 Case 1 & Case 6 (`131`-byte key), and RFC 5869 Case A.1 (`L = 42`).
- **Acceptance evidence at kernel bar:**
  - `lake build` + `lake env leanchecker --fresh` pass.
  - `#guard_msgs in #print axioms` on `pad_injective`, `hmacSha256Spec_length`, `hkdfExpandSpec_length` shows `⊆ [propext, Quot.sound]`; `#print axioms` on `SpecSanityKats` theorems shows `[]` (no axioms at all). Zero `sorry`s.

#### Milestone `M2` — Unrolled `UInt32` SHA-256 Engine & One-Shot Equivalence (`Impl/Sha256Fast`, `Equiv/CompressBridge`)
- **Dependencies:** `M1` *(runs in parallel with `M3`)*.
- **Scope:** Implement high-throughput pure-Lean `UInt32` + 16-word schedule ring-buffer + 64-way unrolled block compression and one-shot `ByteArray` SHA-256; prove compression and one-shot byte equivalence to `Spec.Fips180_4`.
- **Deliverables:**
  - `Impl/Sha256Fast.lean`: `State8`, `loadU32BE`, `storeU32BE`, `compressWords16`, `compressBlockAt` (64-round unrolled over 16-slot ring buffer), `Impl.sha256`.
  - `Equiv/CompressBridge.lean` & `Equiv/Sha256OneShot.lean`: `compressBlockAt_eq_spec`, `compressWords16_eq_spec`, and `sha256_eq_spec (data : ByteArray) (h : data.size < 2 ^ 61) : (Impl.sha256 data).toList = Spec.sha256Bytes data.toList h`.
  - `Tests/Sha256KernelKats.lean`: All 5 CAVP boundary witnesses (`0`, `3`, `55`, `56`, `64` bytes) proved on `Impl.sha256` via `decide +kernel` + `rw [← sha256_eq_spec]`.
- **Acceptance evidence at kernel bar:**
  - `lake build` + `leanchecker --fresh` pass; `#guard_msgs in #print axioms` on `compressBlockAt_eq_spec`, `sha256_eq_spec`, and all 5 `Impl.sha256` boundary KAT theorems shows `⊆ [propext, Classical.choice, Quot.sound]` (zero `Lean.ofReduceBool`, zero `sorry`s).

#### Milestone `M3` — NMAC Midstate Precomputation & Fixed Outer-Block Spec Refinement (`Equiv/PrefixSplit`, `Equiv/OuterBlockBridge`)
- **Dependencies:** `M1` *(runs in parallel with `M2` — touches zero `Impl/` files)*.
- **Scope:** Define the intermediate functional `MidstateRef` model (operating on `Spec.State` and `List UInt8`, precomputing 1-block `innerMidstate` / `outerMidstate` and executing a single 16-word `[d₀..d₇, 0x80000000, 0..0, 0x300]` outer compression) and prove it identical to `Spec.hmacSha256Spec`.
- **Deliverables:**
  - `Equiv/PrefixSplit.lean`: `padZeroCount_add_512`, `parse_pad_block64_prefix` (proving `parse (pad (B₆₄ ++ M)) = block B₆₄ :: parse (padShifted M (512 + 8*|M|))` for `|B₆₄| = 64` and `|M| < 2^61 - 64`), `foldl_compress_prefix64`.
  - `Equiv/OuterBlockBridge.lean`: `parse_pad_outer96_eq_two_blocks` (proving the 96-byte `(K₀ ⊕ opad) ++ innerDigest₃₂` parses into `[opadBlock, outerTemplateBlock innerDigest]`).
  - `Equiv/MidstateSpecEquiv.lean`: `midstateHmac_eq_fips198 (K M : List UInt8) (hK : K.length < 2 ^ 61) (hM : M.length < 2 ^ 61 - 64) : MidstateRef.hmac K M hK hM = Spec.hmacSha256Spec K M hK hM`.
- **Acceptance evidence at kernel bar:**
  - `lake build` + `leanchecker --fresh` pass; `#guard_msgs in #print axioms midstateHmac_eq_fips198` shows `⊆ [propext, Quot.sound]`, zero `sorry`s.

#### Milestone `M4` — Precomputed `HmacKeySchedule`, Streaming `HmacContext`, and End-to-End FIPS 198-1 Equivalence
- **Dependencies:** `M2` and `M3`.
- **Scope:** Implement executable `HmacKeySchedule.ofKey` (both `≤ 64`-byte and `> 64`-byte keys), streaming `HmacContext` (`init`, zero-copy multi-block `update`, zero-allocation outer `finalize`), and one-shot `Impl.hmacSha256`; prove `HmacAbsorbs` chunk-split invariance and compose with `M2` + `M3` to land the headline FIPS 198-1 theorems.
- **Deliverables:**
  - `Impl/HmacKeySchedule.lean` & `Impl/Hmac.lean`.
  - `Equiv/StreamingHmacBridge.lean`: `HmacAbsorbs`, `absorbs_init`, `absorbs_update`, `hmacContext_update_append`, `hmacContext_finalize_eq_midstate`.
  - `Equiv/HmacMain.lean`:
    - `hmacSha256_eq_spec` (one-shot `ByteArray` ↔ `Spec.hmacSha256Spec`)
    - `hmacContext_stream_eq_spec` (arbitrary chunked `List ByteArray` stream ↔ `Spec.hmacSha256Spec` of `ByteArray.flatten`).
- **Acceptance evidence at kernel bar:**
  - `lake build` + `leanchecker --fresh` pass; `#guard_msgs in #print axioms` on `hmacSha256_eq_spec`, `hmacContext_update_append`, and `hmacContext_stream_eq_spec` shows `⊆ [propext, Classical.choice, Quot.sound]`, zero `sorry`s.

#### Milestone `M5` — `HKDF-SHA-256` (RFC 5869) Midstate-Reusing Implementation, Proof & Complete Kernel KAT Suite
- **Dependencies:** `M4` *(runs in parallel with `M6`)*.
- **Scope:** Implement `Impl.hkdfExtract`, midstate-reusing `Impl.hkdfExpand` (`L ≤ 255 * 32`), and `Impl.hkdf`; prove equivalence to `Spec.Rfc5869`; assemble the full kernel-checked test-vector theorem suite (`Tests/KernelKats.lean`) covering all 7 RFC 4231 HMAC cases (including multi-chunk streaming splits) and all 3 RFC 5869 HKDF cases without `native_decide`.
- **Deliverables:**
  - `Impl/Hkdf.lean` & `Equiv/HkdfBridge.lean` (`hkdfExtract_eq_spec`, `hkdfExpand_eq_spec`, `hkdf_eq_spec`).
  - `Tests/KernelKats.lean`: Kernel theorems (`decide +kernel` staged per intermediate digest + `rw` along `hmacSha256_eq_spec` / `hkdf_eq_spec`) for RFC 4231 Cases 1–7, chunked streaming splits at `{0, 1, 63, 64, 65}`, and RFC 5869 Cases A.1–A.3.
- **Acceptance evidence at kernel bar:**
  - `lake build` + `leanchecker --fresh` pass; `#guard_msgs in #print axioms` on `hkdfExtract_eq_spec`, `hkdfExpand_eq_spec`, `hkdf_eq_spec`, and all 10 RFC 4231 + RFC 5869 `Impl` KAT theorems shows `⊆ [propext, Classical.choice, Quot.sound]` (zero `Lean.ofReduceBool`, zero `sorry`s).

#### Milestone `M6` — Ecosystem Bridges, Bulk CAVP/Wycheproof `lean_exe`, and Global Declaration Audit
- **Dependencies:** `M4` (and joins `M5` for the final `Verified.lean` root gate).
- **Scope:** Add a whole-environment MetaM declaration-audit command (verifying *every* public declaration in the library, not just hand-listed theorems, stays inside `[propext, Classical.choice, Quot.sound]`), build the standalone `IO` runner for ~2,000 NIST CAVP + Project Wycheproof vectors, and provide a lightweight zero-dependency interface module matching `libsignal-verify`'s `HmacSha256` contract shape (discharging Trust Item #1 of `libsignal-verify` PR #43 for `key.length < 2^61` and bounded messages, or documenting the exact `< 2^61 - 64` domain refinement).
- **Deliverables:**
  - `Audit/AxiomAudit.lean` & `Verified.lean` (`#guard_msgs` pinning module count, declaration count, and `0` axiom-ceiling offenders).
  - `Adapters/MacContract.lean` (clean `HmacSha256` record + RFC 5869 `hkdfExpand96` specialization theorem).
  - `Tests/CavpWycheproofRunner.lean` (`lean_exe` outside library import closure, parsing vendored `HMAC.rsp`, `SHA256ShortMsg.rsp`, `SHA256LongMsg.rsp`, and Wycheproof HMAC/HKDF JSON vectors).
- **Acceptance evidence at kernel bar:**
  - `lake build` + `lake exe cavp-wycheproof-runner` (~2,000+ vectors pass) + `lake env leanchecker --fresh Verified` all exit `0`; `#guard_msgs` axiom audit reports `0 offenders` outside `[propext, Classical.choice, Quot.sound]`.

---

## 4. Risks and Open Questions

### 4.1 Strategic & Technical Risks That Could Kill or Shrink the Target

1. **Live Pre-Emption in a Fast-Moving Lean Crypto Ecosystem (Medium–High Risk):**
   - Everything decisive in Lean 4 SHA-256 happened within the last six months (`remix7531/fips-180-4-lean` in May 2026; `pure-algebra/lean4-hash`, `kim-em/lean-crypto-hash`, `pyca/verified-garbage`, `thevilledev/ocaml-pq`, and `Beneficial-AI-Foundation/libsignal-verify` PR #43 all in September–October 2026).
   - *Where pre-emption is unlikely:* `pure-algebra/lean4-hash/docs/SHA256-DAG.md` (§1, "Non-goals") explicitly excludes *"SHA-384, SHA-512, HMAC"*, and an org-wide check of `https://api.github.com/users/pure-algebra/repos` confirms none of its 8 repositories touch MACs or KDFs (`lean4-hash` exists solely to support `lean4-whatwg` and `foldlab`).
   - *Where pre-emption is plausible:* (a) `kim-em/lean-crypto-hash` (`4fa361c69f`, pushed `2026-10-22`) already ships executable streaming `Crypto.HMAC` and `hmac_chunking`, lacking only a FIPS 180-4 / 198-1 spec-equivalence proof (and HKDF); if Kim Morrison adds a compression/FIPS bridge and drops `bv_decide`, standalone HMAC shrinks to HKDF + NMAC key-midstate precomputation. (b) `Beneficial-AI-Foundation/libsignal-verify` could discharge its PR #43 `HmacSha256` assumption via Charon/Aeneas over RustCrypto `hmac`/`hkdf`, though an Aeneas Rust proof (`Result`/WP + Aeneas stdlib axioms) would still not provide a zero-dependency pure-Lean executable library.
   - *Mitigation:* Re-run a 2-minute GitHub search (`"hmac" "198-1" language:Lean` and `"hkdf" "5869" language:Lean`) immediately before launching `M1`, and keep **both** NMAC midstate precomputation and RFC 5869 `HKDF-SHA-256` inside the target scope so the artifact remains differentiated even if basic one-shot HMAC lands elsewhere.

2. **Duplication vs. Toolchain/License Fragmentation Politics (Medium Risk):**
   - Building directly on `remix7531/fips-180-4-lean` is blocked for permissive consumers by **`GPL-3.0-or-later`** and a heavyweight **Mathlib (`v4.29.1`)** dependency.
   - Importing `pure-algebra/lean4-hash` (`MIT`, zero deps) pins downstream users to **`v4.33.1` + Lean's `module` system**, inherits `Spec.pad`'s missing `< 2^64` domain guard, and does not expose the internal midstate compression hooks needed by `HmacKeySchedule` and `OuterBlockBridge`.
   - Conversely, shipping a third standalone SHA-256 spec inside an HMAC/HKDF repo invites "yet another SHA-256 spec" pushback unless its relationship to `lean4-hash` and `LeanSha256` is transparent.
   - *Mitigation:* Keep the internal `Spec/Fips180_4.lean` minimal (~200 lines), zero-dependency, and permissively licensed (`Apache-2.0` or `MIT`), and document explicitly why the `< 2^64` (`msg.size < 2^61 - 64`) domain guard and exposed `compress` midstate are required for FIPS 198-1 soundness.

3. **Silent Axiom-Bar Violations (`bv_decide` → `Lean.ofReduceBool`) (High Tactical Risk if Unchecked):**
   - In Lean 4 (`Std.Tactic.BVDecide`), **`bv_decide` relies on `Lean.ofReduceBool` (`Lean.trustCompiler`)** to check LRAT certificates in compiled code — a trap already hit by `kim-em/lean-crypto-hash/validation/CryptoValidation/Proofs.lean` (documented in `pure-algebra/lean4-hash/docs/SHA256-DAG.md`). Any single `bv_decide` or `native_decide` call anywhere in `Equiv/` immediately breaks the strict `[propext, Classical.choice, Quot.sound]` kernel bar!
   - Similarly, reasoning via `ByteArray.toList` (accumulator-based) instead of `bs.data.toList` (`Init/Data/ByteArray/Lemmas.lean`) causes brittle proof blowups.
   - *Mitigation:* Ban `Std.Tactic.BVDecide` by import linter from day 1 (`M1`), prove word equivalences via `Init`'s `rfl` lemmas (`UInt32.toBitVec_and/or/xor/not/shiftLeft/shiftRight/add` + `BitVec.rotateRight_def`), standardize on `bs.data.toList`, and enforce `#guard_msgs in #print axioms` on every milestone.

4. **Kernel WHNF Reduction Time on Multi-Block HMAC/HKDF Test Vectors (Low–Medium Tactical Risk):**
   - Primary-source benchmarks in `pure-algebra/lean4-hash/docs/SHA256-DAG.md` (§2) reveal a sharp runtime-vs-kernel inversion on Lean `v4.33.1`: at runtime `UInt32` is **738× faster** than `BitVec 32`, **but inside Lean's kernel reducer (`decide +kernel`), `BitVec 32` is ~11× faster than `UInt32`** (~`3 ms` vs ~`35 ms` per 64-round compression; ~`1 s` total for a full empty-message SHA-256 digest). Reducing RFC 5869 Case A.2 (~10 block compressions) monolithically over `UInt32` or `ByteArray` could hit multi-second or heartbeat limits.
   - *Mitigation:* Always run `decide +kernel` on a `BitVec 32` / `List UInt8` byte-reference layer (never `UInt32`/`ByteArray`), stage intermediate 32-byte digests (`PRK`, `T(1)`, `T(2)`, `T(3)`) as separate lemmas (~0.2–1.5 s each), and rewrite onto the fast `ByteArray` API via `hkdf_eq_spec`.

5. **Domain-Signature Mismatch Against Unbounded Downstream Contracts (Low Risk):**
   - FIPS 180-4 is defined only for `< 2^64` bits (`< 2^61` bytes), so FIPS 198-1 HMAC-SHA-256 is defined only for `key.size < 2^61` and `msg.size < 2^61 - 64` (and RFC 5869 `HKDF-Expand` for `info.size < 2^61 - 97` and `L ≤ 255 * 32`). Downstream consumers such as `libsignal-verify` PR #43 (`mac : List U8 → List U8 → List U8`) declare total functions without length hypotheses because their call sites pass tiny buffers (e.g., 46-byte labels, 96-byte outputs). `M6`'s adapter must state the `< 2^61 - 64` domain guard on its FIPS-correspondence field while discharging `mac_length = 32` unconditionally.

---

### 4.2 Unresolved Questions (Listed Plainly)

1. **`UNVERIFIED` — Does `sha2-fv` (`remix7531/hashes-fv`) replay cleanly end-to-end today?**
   Because `sha2/proofs/lean/Extraction/` is `.gitignore`d, `.github/workflows/sha2.yml` runs only `cargo build` / `cargo test` (never `make prove` / `lake build`), and our research-only mandate prohibits cloning repositories or running local builds, we verified from committed source that all 35 `.lean` proof files contain zero `sorry`s and depend on `[propext, Classical.choice, Quot.sound, Aeneas.Std.core.fmt.Formatter]`, **but** could not verify live Charon + Aeneas extraction + `lake build` execution.
2. **`UNVERIFIED` — License of `thevilledev/ocaml-pq`:**
   GitHub repository metadata and top-level file inspection for `https://github.com/thevilledev/ocaml-pq` (`ceeb2782e0`) surfaced no `LICENSE` file (`license: null` on the GitHub API). While irrelevant if we write clean-room code from public NIST/IETF standards, no code or proof text from `ocaml-pq` may be copied.
3. **`UNVERIFIED` — Existence of private/unindexed WIP branches for Lean HMAC/HKDF or non-AFP Isabelle fast-code SHA-256:**
   Public GitHub code/repo searches and Brave/Firecrawl web sweeps cover indexed public repositories and the Isabelle Archive of Formal Proofs (`isa-afp.org`), where `Crypto_Standards` (`FIPS180_4`, `FIPS198_1`) provides HOL specs + test vectors. Whether unindexed/private forks (e.g., inside Signal/BAIF, Etheorem, or `kim-em`) already hold unpublished HMAC/HKDF equivalence proofs, or whether non-AFP Isabelle repositories refine `FIPS180_4` to imperative code, cannot be resolved from public sources.
4. **`UNVERIFIED` — Exact `decide +kernel` wall-clock timings for 6-block HMAC (RFC 4231 Case 7) and 10-block HKDF (RFC 5869 Case A.2):**
   Extrapolated from `pure-algebra/lean4-hash`'s measured `1 s` single-block `decide +kernel` timing (`v4.33.1`), staged per-digest lemmas should elaborate in ~`1–3 s` each, **but** exact wall-clock timings on the programme's host VM remain unmeasured until `M1` runs.
5. **Open Programme Policy Question — Target `lean-toolchain` & Repository Home:**
   Current ecosystem artifacts split across Lean `v4.29.0` (`etheorem`), `v4.29.1` (`fips-180-4-lean`), and `v4.33.1` (`lean4-hash` with `module`). Before `M1` starts, the coordinator must choose whether the new HMAC/HKDF lane pins the programme's default toolchain as a standalone zero-dependency package (recommended) or pins `v4.33.1` to permit direct Lake-level bridging to `pure-algebra/lean4-hash`.

---

## What This Dossier Does NOT Show

Because this lane operated strictly under research-only rules (no repository clones, no Lean code written, and no local `lake build` or `leanchecker` executions), all verification claims about external repositories rest on full static inspection of their primary-source `.lean` files, `lakefile`s, `AxiomCheck`/`Verified` gates, and public GitHub Actions workflow run records — **not** on independent local kernel replay on this machine (`leanchecker --fresh` was confirmed in CI logs for `pure-algebra/lean4-hash`, standard `lean-action` CI for `remix7531/fips-180-4-lean`, and Cargo-only CI for `remix7531/hashes-fv`). Furthermore, neither the existing Lean SHA-256 libraries nor the proposed `HMAC-SHA-256` / `HKDF-SHA-256` target prove **cryptographic security reductions** (such as collision resistance, NMAC/HMAC PRF security in the sense of Bellare 2006 / Coq VST's `HMAC256_isPRF.v`, or HKDF IND-CPA computational extract-then-expand security); the scope addressed here is strictly foundational **functional equivalence** to NIST FIPS 180-4, FIPS 198-1, and IETF RFC 5869 under Lean 4's standard kernel axioms.

DOSSIER COMPLETE
