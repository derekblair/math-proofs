# DOSSIER — SHA-256 (FIPS 180-4) Two-Level Formalization & Open Adjacent Targets in Lean 4

- **Date:** 2026-10-26
- **Lane:** `argon-sha256-research-20261026` (Research-only dossier; zero repository or code writes)
- **Baseline audited:** `~/workspace/formalization/research/prior-art-sha256.md` (including its 2026-10-26 Erratum closing Ticket #17)

---

## 1. Prior-Art Sweep (Testing the Standing Claim)

### 1.1 Executive Verdict on Ticket #17 Closure and the Standing Claim

The standing claim from the pre-erratum pass was:

> *"LeanSha256 is implementation-as-spec **AND** the two-level spec+equivalence artifact is open [in Lean 4]."*

- **Conjunct 1 (`LeanSha256` is implementation-as-spec): CONFIRMED.**
  Direct inspection of all 506 lines of [`LeanSha256/Core.lean`](https://raw.githubusercontent.com/etheorem/LeanSha256/main/LeanSha256/Core.lean) and [`README.md`](https://raw.githubusercontent.com/etheorem/LeanSha256/main/README.md) in `etheorem/LeanSha256` (the Reservoir mirror of `etheorem/etheorem/packages/LeanSha256`) confirms there is only a single pure-Lean `UInt32`/`Array`/`ByteArray` implementation (`hash`, `combine`), backed by three `native_decide` FIPS 180-4 §B examples in `Core.lean`, 129 `native_decide` NIST CAVP vectors in `LeanSha256Tests/Nist.lean` (introducing `Lean.ofReduceBool`), and 19 shape/size lemmas (`ch_eq_fips`…`smallSigma1_eq_fips` by `rfl`, constant array sizes and endpoints, `pad_size_multiple_of_64`, `hash_size_eq_32`). `Core.lean` lines 318–321 state explicitly: *"Kernel-checked theorems that fix the shape of the spec against FIPS 180-4. They don't claim 'computes SHA-256'. That's an empirical question against NIST vectors."*
- **Conjunct 2 (the two-level spec+equivalence artifact is open in Lean 4): REFUTED** for **one-shot, byte-aligned SHA-256 (and SHA-224/384/512/512-224/512-256)**.
  Direct source audit of all 57 `.lean` files in [`remix7531/fips-180-4-lean`](https://github.com/remix7531/fips-180-4-lean) confirms a genuine three-tree development (`spec/`, `impl/`, `equiv/`) where an independent bitwise FIPS 180-4 specification over `Message := List Bool` and `BitVec 32` is proved equal to a distinct, performance-tuned (~170 MiB/s) unrolled `UInt32` implementation over `ByteArray` via `SHS.Equiv.SHA256.compress_correct`, `sha256_correct`, and `sha224_correct` ([`equiv/SHA256/Main.lean`](https://raw.githubusercontent.com/remix7531/fips-180-4-lean/main/equiv/SHA256/Main.lean)), with **zero `sorry`s, zero custom axioms, and pinned `[propext, Classical.choice, Quot.sound]` via `#guard_msgs in #print axioms`** ([`equiv/AxiomCheck.lean`](https://raw.githubusercontent.com/remix7531/fips-180-4-lean/main/equiv/AxiomCheck.lean)), and green GitHub Actions CI ([run `26441432411`](https://github.com/remix7531/fips-180-4-lean/actions/runs/26441432411) on `HEAD` `0018b08f`). Furthermore, we located the previously uninspected repository behind `sha2-fv`: [`remix7531/hashes-fv`](https://github.com/remix7531/hashes-fv), by the same author, which chains Aeneas-extracted RustCrypto one-shot SHA-2 functions through `fips-180-4-lean`'s `sha256_correct`.
- **Closure assessment:** Closing Ticket #17 (one-shot SHA-256 spec + equivalence) was **correct**. However, primary-source inspection also reveals crisp, high-value gaps that remain genuinely **OPEN** in open-source Lean 4: (1) **no verified incremental/streaming `init`/`update`/`finalize` SHA-256 state machine** exists anywhere in Lean (`fips-180-4-lean` is one-shot `ByteArray → Vector UInt8 32`, and `hashes-fv` explicitly deleted RustCrypto's streaming `Digest` trait API to verify one-shot slices only); (2) **no open-source two-level formalization of HMAC-SHA-256 (FIPS 198-1 / RFC 2104)** exists in Lean 4 (and one prominent single-level repo, `SentinelOps-CI/lean-toolchain`, actually implements non-RFC-compliant over-long key handling); and (3) `fips-180-4-lean` is **`GPL-3.0-or-later`**, dormant since May 2026 on `v4.29.1`, and pulls in full `Mathlib` + `mdgen` even for `spec/`, preventing adoption by MIT/Apache-2.0 zero-dependency Lean projects.

---

### 1.2 Primary-Source Deep Audit of the Two Decisive Lean Artifacts

#### A. `remix7531/fips-180-4-lean`
- **Primary sources read:** GitHub API repo/tree/workflow metadata (`https://api.github.com/repos/remix7531/fips-180-4-lean`), [`README.md`](https://raw.githubusercontent.com/remix7531/fips-180-4-lean/main/README.md), [`lakefile.lean`](https://raw.githubusercontent.com/remix7531/fips-180-4-lean/main/lakefile.lean), [`lean-toolchain`](https://raw.githubusercontent.com/remix7531/fips-180-4-lean/main/lean-toolchain), [`spec/Setup.lean`](https://raw.githubusercontent.com/remix7531/fips-180-4-lean/main/spec/Setup.lean), [`spec/Functions.lean`](https://raw.githubusercontent.com/remix7531/fips-180-4-lean/main/spec/Functions.lean), [`spec/Preprocessing.lean`](https://raw.githubusercontent.com/remix7531/fips-180-4-lean/main/spec/Preprocessing.lean), [`spec/HashAlgorithms.lean`](https://raw.githubusercontent.com/remix7531/fips-180-4-lean/main/spec/HashAlgorithms.lean), [`spec/SHA512t.lean`](https://raw.githubusercontent.com/remix7531/fips-180-4-lean/main/spec/SHA512t.lean), [`impl/SHA256.lean`](https://raw.githubusercontent.com/remix7531/fips-180-4-lean/main/impl/SHA256.lean), [`equiv/README.md`](https://raw.githubusercontent.com/remix7531/fips-180-4-lean/main/equiv/README.md), [`equiv/AxiomCheck.lean`](https://raw.githubusercontent.com/remix7531/fips-180-4-lean/main/equiv/AxiomCheck.lean), [`equiv/SHA256/Main.lean`](https://raw.githubusercontent.com/remix7531/fips-180-4-lean/main/equiv/SHA256/Main.lean), [`equiv/SHA256/Padding/Equiv.lean`](https://raw.githubusercontent.com/remix7531/fips-180-4-lean/main/equiv/SHA256/Padding/Equiv.lean), [`equiv/SHA256/Padding/Parsing.lean`](https://raw.githubusercontent.com/remix7531/fips-180-4-lean/main/equiv/SHA256/Padding/Parsing.lean), [`tests/CAVP.lean`](https://raw.githubusercontent.com/remix7531/fips-180-4-lean/main/tests/CAVP.lean), [`.github/workflows/ci.yml`](https://raw.githubusercontent.com/remix7531/fips-180-4-lean/main/.github/workflows/ci.yml), [`.refactor/WARTS.md`](https://raw.githubusercontent.com/remix7531/fips-180-4-lean/main/.refactor/WARTS.md), plus a full keyword scan (`sorry`, `admit`, `axiom `, `native_decide`, `bv_decide`, `extern`, `implemented_by`, `unsafe `) across all 57 `.lean` files.
- **Exact theorem statements** (quoted verbatim from [`equiv/SHA256/Main.lean`](https://raw.githubusercontent.com/remix7531/fips-180-4-lean/main/equiv/SHA256/Main.lean), lines 36–81, inside `namespace SHS.Equiv.SHA256`):
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
  (Five parallel theorems — `compress_correct`, `sha512_correct`, `sha384_correct`, `sha512_256_correct`, `sha512_224_correct` — are proved in `equiv/SHA512/Main.lean`.)
- **Is `spec/` genuinely independent of `impl/`?** **Yes — completely distinct data representations, control flow, schedule layout, and padding mechanics:**
  1. *Spec (`spec/`):* Models messages at the bit level (`abbrev Message := List Bool`), words as `BitVec 32`, blocks as `Vector (BitVec 32) 16`, schedules as full 64-word arrays `Vector (BitVec 32) 64`, and digests as `BitVec 256` (`spec/Setup.lean`, `spec/Functions.lean`). Padding (`spec/Preprocessing.lean` lines 45–52) mirrors FIPS 180-4 §5.1.1 literally using modular congruence search `let k := min { k < 512 | ℓ + 1 + k ≡ 448 [MOD 512] }` and appends `[true] ++ List.replicate k false ++ (List.range 64).reverse.map ℓ.testBit`. Parsing (`spec/Preprocessing.lean` lines 114–121) chunks the bit list via `M.toChunks 512` and `b.toChunks 32 |>.map Word.fromBits`. `SHS.SHA256.schedule` and `compress` (`spec/HashAlgorithms.lean` lines 225–267) pre-compute all 64 schedule words in `Id.run do` before running a 64-step mutable `a..h` loop, and `sha256` concatenates `H[0] ++ … ++ H[7] : BitVec 256`.
  2. *Impl (`impl/SHA256.lean`):* Operates over byte-aligned `ByteArray` inputs, machine `UInt32` words with shift/or rotation `(x >>> n) ||| (x <<< (32 - n))` (avoiding `BitVec` `Nat` allocations), an unboxed-field `RoundState` struct (`schedule : Vector UInt32 16` plus eight scalar `UInt32` fields `a..h`), and a **fused 16-word circular ring-buffer schedule** mutated in place at slot `i % 16` inside a **64-fold compile-time unrolled loop** (`SHS.Impl.Unroll.unroll64 roundStep init`). Full blocks read bytes directly from `data` at offset `i * 64` via a 16-way unrolled `toU32sFromBytes` without intermediate `Vector UInt8 64` allocation; the final 1 or 2 blocks (`remaining < 56` vs `remaining ≥ 56`) are constructed directly as `Vector UInt8 64` blocks with big-endian `UInt64` bit length (`data.size.toUInt64 <<< 3`), after guarding `if 2 ^ 61 ≤ data.size then panic! …`.
  3. *Non-triviality of `equiv/`:* Bridging these two layers requires ~190 KB of proof across 23 modules (`equiv/Common/*` + `equiv/SHA256/*`), including a nontrivial circular-queue invariant (`MatchAfter` in `equiv/SHA256/Compress/Match.lean`) relating the 16-slot ring buffer at round $t$ to `W[t-16 .. t-1]` of the 64-word spec schedule, plus a 4-file byte-vs-bit padding/parsing equivalence (`equiv/SHA256/Padding/{Layout,ByteDecoding,Parsing,Equiv}.lean`).
- **`sorry` / `axiom` / `native_decide` status:**
  - Across all 57 `.lean` files: **0 `sorry`**, **0 `admit`**, **0 `axiom` declarations**, **0 `bv_decide` invocations**, **0 `@[extern]` / `@[implemented_by]` / `unsafe`**.
  - [`equiv/AxiomCheck.lean`](https://raw.githubusercontent.com/remix7531/fips-180-4-lean/main/equiv/AxiomCheck.lean) enforces compile-time regression gates on all eight public theorems via `#guard_msgs in #print axioms …`, pinning the exact list `[propext, Classical.choice, Quot.sound]`.
  - GitHub Actions workflow [`.github/workflows/ci.yml`](https://raw.githubusercontent.com/remix7531/fips-180-4-lean/main/.github/workflows/ci.yml) runs `leanprover/lean-action@v1` with `build-args: "spec impl equiv tests"` and `lint: "true"`, followed by `make test` (all 1,415 CAVP vectors via the compiled `lake exe cavp` binary). The latest CI run on `main` (`0018b08f`, [run `26441432411`](https://github.com/remix7531/fips-180-4-lean/actions/runs/26441432411), 2026-05-26) completed with **`conclusion: success`**.
  - *Minor hygiene note:* `spec/SHA512t.lean` lines 72 and 102 contain two standalone `example` blocks using `by native_decide` to check that the generic `H0_t` IV generator agrees with the literal `H0_512_224` and `H0_512_256` constants; neither `example` is imported into `equiv/` or enters any theorem's axiom footprint (`equiv/SHA256/Lift.lean:55` explicitly notes avoiding `native_decide` so `Lean.ofReduceBool` never enters the trust base).
- **Scope audit:**
  - *One-shot vs. streaming (`init`/`update`/`finalize`):* **One-shot only.** Although comments in `impl/SHA256.lean` say *"Streaming-padded SHA-256"*, that phrase refers strictly to iterating over an in-memory `data : ByteArray` in one call (`def sha256 (data : ByteArray) : Vector UInt8 32`) without allocating a padded `ByteArray` copy. There is **no** stateful hasher context, **no** partial-block byte buffer across `update` calls, **no** `init` / `update` / `finalize` API, and **no** chunk-split invariance theorem. Moreover, `impl/` and `equiv/` handle **byte-aligned** inputs (`ByteArray`, `data.size < 2^61`) only; non-byte-aligned bit strings are handled by `spec/` alone (`tests/CAVP.lean:55` returns `none` from `implSha256Hash` when `len % 8 ≠ 0`).
  - *Padding proved?* **Yes, for impl↔spec correspondence on byte-aligned inputs (`< 2^61` bytes):** `implPaddedBlocks_lift_eq_parsePad` (`equiv/SHA256/Padding/Parsing.lean:155`) proves `(implPaddedBlocks data).map (toSpecBlock ∘ Impl.toU32s) = SHS.SHA256.parse (SHS.SHA1.pad (bytesToBitMessage data))`, covering full blocks, 1-block finish (`data.size % 64 < 56`), and 2-block spill (`data.size % 64 ≥ 56`). Cryptographic domain-separation lemmas on `SHS.SHA256.pad` itself (e.g., injectivity / suffix-freeness `pad M₁ = pad M₂ → M₁ = M₂` for Merkle–Damgård reductions) are **not** proved.
  - *SHA-224 included?* **Yes** (`SHS.SHA256.sha224`, `Impl.sha224`, `sha224_correct`), plus SHA-384, SHA-512, SHA-512/224, SHA-512/256. SHA-1 is spec-only (`README.md` line 44; `spec/HashAlgorithms.lean:782` notes `sha1 = sha1_alt` is unproved).
- **Activity, toolchain, dependencies, and license:**
  - Created `2026-04-20`, last push `2026-05-26T08:31:56Z` (~5 months inactive as of 2026-10-26); 0 stars, 0 forks, 0 issues; single author (`remix7531`); not registered on Reservoir.
  - Toolchain pinned to `leanprover/lean4:v4.29.1`, requiring full `mathlib4 @ v4.29.1` and `Seasawher/mdgen @ v4.29.0-rc8` (`lakefile.lean`).
  - License: **`GPL-3.0-or-later`** ([`LICENSE`](https://raw.githubusercontent.com/remix7531/fips-180-4-lean/main/LICENSE) and `README.md` line 63).

#### B. `sha2-fv` (`remix7531/hashes-fv`)
- **Repository located & inspected:** Queries against the crates.io API (`https://crates.io/api/v1/crates/sha2-fv`) and crate archive (`https://static.crates.io/crates/sha2-fv/sha2-fv-0.1.0.crate`) resolve `sha2-fv` v0.1.0 to [`https://github.com/remix7531/hashes-fv`](https://github.com/remix7531/hashes-fv) (published `2026-05-28` by the **same author**, `remix7531`). All 35 `.lean` files and 6 `.rs` files in `hashes-fv` (`master` branch) and in `sha2-fv-0.1.0.crate` were read directly.
- **Architecture & exact theorem statements:**
  `hashes-fv` forks RustCrypto's `sha2` crate, **deletes upstream's `digest::Digest` streaming (`new`/`update`/`finalize`) trait API and all SIMD/assembly backends** ([`sha2/README.md`](https://raw.githubusercontent.com/remix7531/hashes-fv/master/sha2/README.md) lines 13 & 66), leaving 333 LOC of portable one-shot Rust (`sha256(data: &[u8]) -> [u8; 32]`, `sha224`, `sha512`, `sha384`, `sha512_256`, `sha512_224`, plus hazmat `compress256`/`compress512` in [`sha2/src/lib.rs`](https://raw.githubusercontent.com/remix7531/hashes-fv/master/sha2/src/lib.rs)). Charon + Aeneas (`remix7531/aeneas @ sha2-fv-pin`, Lean `v4.29.1`) translate the Rust functions into monadic Lean definitions (`Extraction.*`), which `sha2/proofs/lean/Sha256/ImplSpec.lean` refines to `fips-180-4-lean`'s `Impl.sha256` and [`sha2/proofs/lean/Sha256.lean`](https://raw.githubusercontent.com/remix7531/hashes-fv/master/sha2/proofs/lean/Sha256.lean) chains through `SHS.Equiv.SHA256.sha256_correct`:
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
- **`sorry` / `axiom` / CI verification status:**
  - Across all 35 hand-written `.lean` files: **0 `sorry`**, **0 `admit`**, **0 `native_decide` / `bv_decide`**.
  - **Extra non-standard axiom:** Per [`sha2/README.md`](https://raw.githubusercontent.com/remix7531/hashes-fv/master/sha2/README.md) line 39, the pinned axiom set is `{propext, Classical.choice, Quot.sound, Aeneas.Std.core.fmt.Formatter}` (a 4th Aeneas-model opacity axiom arising from `try_into().unwrap()` panic formatting in Rust). Moreover, [`sha2/proofs/lean/AxiomCheck.lean`](https://raw.githubusercontent.com/remix7531/hashes-fv/master/sha2/proofs/lean/AxiomCheck.lean) issues bare `#print axioms` commands *without* `#guard_msgs` assertions.
  - **Build / CI gap (marked UNVERIFIED for automated CI proof replay):** Both the git tree (`remix7531/hashes-fv`) and the published `sha2-fv-0.1.0.crate` tarball omit the Aeneas-generated `Extraction/Funs.lean` and `Extraction/Types.lean` files (which `sha2/Makefile` regenerates via Charon + Aeneas in `make extract`), and [`.github/workflows/sha2.yml`](https://raw.githubusercontent.com/remix7531/hashes-fv/master/.github/workflows/sha2.yml) runs only `cargo build`, `cargo test`, and `cargo fmt` — it never runs `make extract` or `make prove` (`lake build`). Thus, while the 35 Lean proof files contain zero `sorry`s by direct inspection, end-to-end Lean kernel acceptance of `sha256_spec` on `master` is **UNVERIFIED by public CI** without building the Nix Charon/Aeneas toolchain locally.
  - **Activity & license:** Created `2026-05-07`, last pushed `2026-05-28T15:47:34Z` (61 crates.io downloads). Rust code is `MIT OR Apache-2.0`; Lean proofs under `sha2/proofs/lean/` are **`GPL-3.0-or-later`** (inherited from `fips-180-4-lean`, per `sha2/README.md` line 72).

---

### 1.3 Comprehensive Sweep Table (Lean 4 & Non-Lean Verification Systems)

| Artifact / System | Primary Source Inspected | System & License | What Exists & Exact Scope | Verification / Completeness Status |
|---|---|---|---|---|
| **`remix7531/fips-180-4-lean`** | [Repo](https://github.com/remix7531/fips-180-4-lean), all 57 `.lean` files, [CI run](https://github.com/remix7531/fips-180-4-lean/actions/runs/26441432411) | Lean 4.29.1 + Mathlib + mdgen · `GPL-3.0-or-later` | Literate FIPS 180-4 bitwise `spec/` (SHA-1 + all 6 SHA-2 variants), ~170 MiB/s unrolled `UInt32` `impl/` (all 6 SHA-2 variants), `equiv/` proving `compress_correct`, `sha256_correct`, `sha224_correct`, `sha512_correct`, `sha384_correct`, `sha512_256_correct`, `sha512_224_correct` for one-shot `ByteArray` (`size < 2^61`) | **Complete for one-shot byte-aligned SHA-2.** Zero `sorry`s; `#guard_msgs in #print axioms` pins `[propext, Classical.choice, Quot.sound]`; green CI + 1,415 CAVP vectors. **No streaming `init`/`update`/`finalize` API; GPL-3.0; dormant since 2026-05-26.** |
| **`sha2-fv` (`remix7531/hashes-fv`)** | [Crates.io API](https://crates.io/api/v1/crates/sha2-fv), [Repo](https://github.com/remix7531/hashes-fv), all 35 `.lean` & 6 `.rs` files | Rust + Charon/Aeneas + Lean 4.29.1 · Rust `MIT/Apache-2.0`, Proofs `GPL-3.0-or-later` | Refactored one-shot RustCrypto SHA-2 (`sha256`, `sha224`, `sha512`, `sha384`, `sha512_256`, `sha512_224`; streaming `Digest` trait stripped) refined in Lean to `fips-180-4-lean`'s `Impl` and `spec` (`sha256_spec`, `sha224_spec`, etc.) | **Zero `sorry`s in 35 inspected `.lean` files**, uses 4th axiom `Aeneas.Std.core.fmt.Formatter`. `Extraction/{Funs,Types}.lean` omitted from git/crate and GHA runs Rust tests only (**Lean build UNVERIFIED in CI**). One-shot only. |
| **`LeanSha256` (`etheorem/etheorem`)** | [Mirror](https://github.com/etheorem/LeanSha256), [`Core.lean`](https://raw.githubusercontent.com/etheorem/LeanSha256/main/LeanSha256/Core.lean) (506 lines), [`README.md`](https://raw.githubusercontent.com/etheorem/LeanSha256/main/README.md) | Lean 4 (zero deps) · `LGPL-3.0` | Pure-Lean one-shot `hash : ByteArray → ByteArray` and `combine` (`hash (l ++ r)`). Reservoir-indexed v0.1.0 | **Implementation-as-spec.** Zero `sorry`/FFI; 19 shape/size lemmas (`rfl`/array lengths); 3 FIPS §B + 129 CAVP gates via `native_decide` (`Lean.ofReduceBool`). Note: `Core.pad` wraps bit-length mod $2^{64}$ without a `< 2^{61}` guard. |
| **`SizzLean` + `LeanHazmatSha256` (`etheorem/etheorem`)** | [`Sha256.lean`](https://raw.githubusercontent.com/etheorem/etheorem/main/packages/SizzLean/SizzLean/Hasher/Sha256.lean), [`Sha256Equiv.lean`](https://raw.githubusercontent.com/etheorem/etheorem/main/packages/SizzLean/SizzLean/Hasher/Sha256Equiv.lean), [`Sha256Batch.lean`](https://raw.githubusercontent.com/etheorem/etheorem/main/packages/SizzLean/SizzLean/Hasher/Sha256Batch.lean) | Lean 4 + OpenSSL/ISA-L C FFI · `LGPL-3.0` | Generic SSZ Merkleization wired to `@[extern] opaque` OpenSSL/ISA-L C shims via 3 explicit `axiom`s: `sha256Hash_eq_spec`, `sha256Combine_eq_spec`, `sha256BatchCombine_eq_spec` | **Axiomatized FFI bridge.** Because `LeanHazmat.Sha256.*` are `@[extern] opaque` C calls, these 3 axioms **cannot** be proved in Lean without a formal C/OpenSSL semantics; only a pure-Lean `@[csimp]` replacement can avoid them. |
| **`ProofOfKeags/btc-verified`** | [Repo](https://github.com/ProofOfKeags/btc-verified), [`Crypto/README.md`](https://raw.githubusercontent.com/ProofOfKeags/btc-verified/master/BtcVerified/Crypto/README.md), [`Crypto/Sha256.lean`](https://raw.githubusercontent.com/ProofOfKeags/btc-verified/master/BtcVerified/Crypto/Sha256.lean), [`Impl/README.md`](https://raw.githubusercontent.com/ProofOfKeags/btc-verified/master/BtcVerified/Impl/README.md) | Lean 4 · `Apache-2.0` (active 2026-10-26) | Computable `sha256` and `sha256d : List UInt8 → List UInt8`, proving `sha256_length` and `collisionResistant_sha256_iff_sha256d`; two-level `Impl/` verifies Bitcoin Core's `ComputeMerkleRoot` | **Implementation-as-spec for SHA-256.** Standard axioms only, no `sorry`, no `native_decide`; golden vectors & mainnet block headers checked, but no separate FIPS 180-4 bitwise spec or streaming SHA-256. |
| **`keithadler/lean-x509` & `lean-pkcs7cms`** | [Repo](https://github.com/keithadler/lean-x509), [`X509/Sha256.lean`](https://raw.githubusercontent.com/keithadler/lean-x509/main/X509/Sha256.lean), [`X509/Real.lean`](https://raw.githubusercontent.com/keithadler/lean-x509/main/X509/Real.lean), [`test/Axioms.lean`](https://raw.githubusercontent.com/keithadler/lean-x509/main/test/Axioms.lean) | Lean 4.35.0 (zero deps) · `MIT` (pushed 2026-10-16) | ~135-line pure `Nat`-word one-shot `X509.Sha256` designed for fast GMP kernel reduction (`decide +kernel`) over real X.509 certificate chains and FIPS §B vectors | **Implementation-as-spec.** Zero `sorry`, strictly `[propext, Classical.choice, Quot.sound]` (`test/Axioms.lean`). Demonstrates `decide +kernel` smoothly evaluates multi-KB SHA-256 digests in the kernel when written over `Nat` words. |
| **`SentinelOps-CI/lean-toolchain`** | [Repo](https://github.com/SentinelOps-CI/lean-toolchain), [`SHA256.lean`](https://raw.githubusercontent.com/SentinelOps-CI/lean-toolchain/main/LeanToolchain/Crypto/SHA256.lean), [`HMAC.lean`](https://raw.githubusercontent.com/SentinelOps-CI/lean-toolchain/main/LeanToolchain/Crypto/HMAC.lean) | Lean 4 · `MIT` (pushed 2026-07-18) | One-shot `sha256` and `hmacSha256` over `ByteArray` + custom Rust codegen | **Shape/size lemmas only (`sha256_size`, `rfl` determinism).** Notably, `HMAC.lean` lines 13–23 & 40–51 **violate RFC 2104 / FIPS 198-1 for keys $> 64$ bytes** (omits zero-padding the 32-byte key hash to 64 bytes before XOR). |
| **`AfonsoBitoque/LeanServer` & `LeanServerWASM`** | [LeanServer](https://github.com/AfonsoBitoque/LeanServer), [`Crypto/SHA256.lean`](https://raw.githubusercontent.com/AfonsoBitoque/LeanServer/main/LeanServer/Crypto/SHA256.lean), [LeanServerWASM](https://github.com/AfonsoBitoque/LeanServerWASM) | Lean 4.27.0 → C/WASM · `Apache-2.0` | Pure-Lean `sha256`, `hmac_sha256`, `hkdf_extract` compiled to WASM for TLS 1.3 | **Implementation-as-spec.** Only output-length (`= 32`) and determinism proved (`LeanServerWASM/README.md` line 35); no independent FIPS 180-4 / 198-1 spec equivalence. |
| **`reilabs/freigen` (+ BitZ) & `eKisNonos/sha256-gf2-r1cs`** | [`reilabs/freigen`](https://github.com/reilabs/freigen) ([`Model.lean`](https://raw.githubusercontent.com/reilabs/freigen/main/Freigen/F2Z/Examples/Sha256/Model.lean), [`Correctness.lean`](https://raw.githubusercontent.com/reilabs/freigen/main/Freigen/F2Z/Examples/Sha256/Correctness.lean)), [ePrint 2026/2141](http://eprint.iacr.asia/2026/2141.pdf), [`sha256-gf2-r1cs`](https://github.com/eKisNonos/sha256-gf2-r1cs) | Lean 4 · No license declared | ZK circuit arithmetizations over $\mathbb{F}_2$ / R1CS of SHA-256 compression (`permCirc'_complete`, `permCirc'_sound`, 7,145 columns) and fixed 2 KB fast witness generation | **ZK circuit soundness/completeness against a local compression model**, with `native_decide` on 3 block examples. Not a general FIPS 180-4 hash/padding formalization. |
| **`leanprover/LNSym` & `spitters/CatCrypt-core`** | [`LNSym`](https://github.com/leanprover/LNSym) tree, [`CatCrypt-core`](https://github.com/spitters/CatCrypt-core) tree, [ePrint 2026/604](http://eprint.iacr.asia/2026/604.pdf) | Lean 4 · `Apache-2.0` / `MIT` | `LNSym`: ARMv8 symbolic verification + LRAT bit-blasting of **SHA-512** (`Specs/SHA512.lean`, `Proofs/SHA512/`). `CatCrypt`: game-based/QROM protocol proofs assuming HKDF-SHA256 / translated libcrux specs | **Adjacent only.** Neither repository formalizes SHA-256 or proves a SHA-256 implementation equivalent to FIPS 180-4. |
| **`proofbundle/lean-sha-256` & `lean-hmac-sha-256` (+ siblings)** | [`lean-sha-256`](https://github.com/proofbundle/lean-sha-256) ([`PROOF_STATUS.json`](https://raw.githubusercontent.com/proofbundle/lean-sha-256/main/PROOF_STATUS.json)), [`lean-hmac-sha-256`](https://github.com/proofbundle/lean-hmac-sha-256) | Lean 4 · `GPL-3.0-or-later` header (no repo license) | Auto-generated registry stubs (`state: "SCAFFOLDED"`); `.lean` files contain only string metadata (`def algorithmId := "SHA-256"`) | **Empty scaffolds (zero SHA/HMAC definitions or theorems).** Audited explicitly so repo titles do not cause false-positive closures. |
| **Lema (`LorenaLabs/lema-lang`)** | [`lema-lang.org` Stdlib](https://www.lema-lang.org/docs/reference/standard-library/), [HTTPS stack](https://www.lema-lang.org/docs/explanation/https-stack/), [Set-up](https://www.lema-lang.org/docs/tutorials/set-up/) | Custom Lema store over Lean 4.34.1 · Proprietary / unreleased repo | Docs describe one-shot `Sha256Spec` / `Sha256Unboxed` (`digestSlice_eq_spec`) and `Hmac` (`hmacSpec`, `hmacSpec_congr`, RFC 4231 cases 1–7) | **UNVERIFIED (documentation-grade only).** Referenced git URL `https://github.com/LorenaLabs/lema-lang.git` returns **HTTP 404 Not Found**; source, theorem statements, and axioms cannot be audited, and it is not an open/importable Lake library. |
| **Lean 4 Core, Mathlib4, Batteries** | GitHub code/tree searches & `prior-art-sha256.md` | Lean 4 · `Apache-2.0` | None | **Absent.** Neither core Lean, Batteries, nor Mathlib4 contains SHA-256, FIPS 180-4, or HMAC. |
| **Coq / Rocq: Appel VST + OpenSSL SHA-256 & HMAC** | [Appel TOPLAS 2015](https://www.cs.princeton.edu/~appel/papers/verif-sha-2.pdf), [Beringer et al. USENIX 2015](https://www.cs.princeton.edu/~appel/papers/verified-hmac.pdf), [`PrincetonUniversity/VST`](https://github.com/PrincetonUniversity/VST) | Coq/Rocq + VST + CompCert + FCF | Pure functional FIPS 180-4 spec (`SHA256.v`), block/streaming intermediate spec, Verifiable C proof of OpenSSL's stateful `SHA256_Init`/`Update`/`Final` and `HMAC`, plus FCF game-based PRF reduction | **Gold-standard complete two/three-level artifact** (~9k LOC Coq for SHA-256), explicitly covering stateful streaming (`Init`/`Update`/`Final`) and HMAC. |
| **F\* / Low\*: HACL\*, EverCrypt/Vale, Cryspen `libcrux`** | [HACL\* CCS 2017](https://eprint.iacr.org/2017/536.pdf), [`hacl-star`](https://github.com/hacl-star/hacl-star), [`cryspen/libcrux`](https://github.com/cryspen/libcrux) | F\* / Low\* / Vale / Rust+`hax` · `Apache-2.0` | Pure mathematical `Spec.Agile.Hash` / `Spec.Agile.HMAC` + verified C (`Hacl.Hash.SHA2`), x86/ARM assembly (EverCrypt), **verified agile streaming functor (`Hacl.Streaming.MD` ↔ `Spec.Hash.Incremental`)**, and verified Rust (`libcrux-sha2`). Shipped in Firefox, Linux, CPython | **Complete & deployed at scale**, including streaming state machines and HMAC/HKDF. |
| **Cryptol + SAW (Galois / AWS-LC)** | [`GaloisInc/cryptol-specs`](https://github.com/GaloisInc/cryptol-specs), [CAV/Springer AWS-LC paper](https://link.springer.com/content/pdf/10.1007/978-3-030-81685-8_31.pdf), [`aws/aws-lc`](https://github.com/aws/aws-lc) | Cryptol + SAW (SMT/ABC bit-blasting) · `Apache-2.0` | Executable Cryptol FIPS 180-4 & HMAC specs + symbolic equivalence proofs of BoringSSL-lineage AWS-LC C + x86-64/ARM assembly (including stateful `EVP_DigestUpdate` and HMAC-SHA-256/384/512) | **Complete for production C/ASM**, relying on SAW symbolic execution + SAT/SMT solvers rather than a foundational LCF/type-theory kernel. |
| **Isabelle/HOL: AFP `Crypto_Standards`** | [AFP `Crypto_Standards`](https://www.isa-afp.org/entries/Crypto_Standards.html) (`FIPS180_4`, `FIPS198_1`, `FIPS180_4_Test_Vectors`) | Isabelle/HOL · `BSD` | Literate mechanization of FIPS 180-4 (SHA-1 and all 6 SHA-2 functions) and FIPS 198-1 (HMAC), with NIST test-vector theories evaluated inside Isabelle | **Complete standards specification + HMAC + vectors** in Isabelle/HOL (spec-centric rather than C/streaming refinement). |
| **Jasmin + EasyCrypt (`libjade`) & HOL4 / CakeML** | [`formosa-crypto/libjade`](https://github.com/formosa-crypto/libjade), [`CakeML/cakeml`](https://github.com/CakeML/cakeml) | Jasmin/EasyCrypt (`MIT/CC0`); HOL4/CakeML (`BSD`) | `libjade`: verified x86-64 Jasmin SHA-256 proved functionally correct & constant-time in EasyCrypt. CakeML: HOL4 SHA-256 spec compiled end-to-end to verified machine code | **Complete in their respective toolchains**, further underscoring that streaming/stateful SHA-256 and HMAC are mature outside Lean 4. |

---

## 2. Spec Architecture for the Best Remaining Open Target

### 2.1 Candidate Evaluation at the Programme's Bar

Given that one-shot SHA-256 and SHA-224 are taken in Lean 4 by `remix7531/fips-180-4-lean` (and bridged to one-shot Rust in `remix7531/hashes-fv`), we evaluate all five candidate SHA-256-adjacent targets from the brief against our primary-source findings:

| Candidate Target | Status in Open-Source Lean 4 | Evaluation & Verdict |
|---|---|---|
| **1. Discharging SizzLean's three `*_eq_spec` FFI axioms (`sha256Hash_eq_spec`, `sha256Combine_eq_spec`, `sha256BatchCombine_eq_spec`)** | Axiomatized in `etheorem/etheorem` (`Sha256Equiv.lean`, `Sha256Batch.lean`) | **REJECT (logically unprovable as stated; narrow as `@[csimp]`).** In `LeanHazmatSha256`, those three functions are `@[extern] opaque` C FFI calls into `sha256_shim.c` / `sha256_batch.c` (OpenSSL `EVP_*` + Intel ISA-L multi-buffer). An `@[extern] opaque` has no kernel body in Lean 4, so `@LeanHazmat.Sha256.sha256Hash = LeanSha256.hash` cannot be proved without formalizing C, OpenSSL, ISA-L x86-64 assembly, and the Lean FFI ABI (`Sha256Equiv.lean` lines 25–31 explicitly note this). Replacing FFI with a pure-Lean `@[csimp]` theorem is possible (after matching `LeanSha256.Core.pad`'s silent mod-$2^{64}$ length wraparound at $\ge 2^{61}$ bytes), but gives up SizzLean's SIMD multi-buffer speed and adds no new mathematical specification. |
| **2. SHA-224 (FIPS 180-4 §6.3)** | **TAKEN** (`fips-180-4-lean` + `hashes-fv`) | **REJECT.** Both `SHS.Equiv.SHA256.sha224_correct` (`equiv/SHA256/Main.lean:227`, standard axioms only, CAVP-tested) and Rust's `sha224_spec` (`hashes-fv`) are already complete. |
| **3. Maintained standalone spec library others can import (`Init`-only, permissive license)** | **PARTIAL GAP** (`fips-180-4-lean` is `GPL-3.0-or-later`, dormant on `v4.29.1`, requires `Mathlib` + `mdgen`) | **FOLD INTO FOUNDATION LAYER (do not run alone).** Downstream MIT/Apache-2.0 Lean repos (`btc-verified`, `lean-x509`, `CatCrypt`, `LeanServer`) cannot legally import `GPL-3.0` code and avoid `Mathlib` bloat for crypto primitives. However, shipping *only* a re-proved one-shot SHA-256 under `Apache-2.0` would duplicate `fips-180-4-lean`'s theorem shape. It should instead serve as **Layer 0** of the genuinely open stateful/construction targets below. |
| **4. Streaming `init` / `update` / `finalize` SHA-256 API proved equivalent to the one-shot FIPS 180-4 spec** | **OPEN** across all inspected Lean 4 repos | **SELECT (Core Engine).** Completely absent in Lean 4: `fips-180-4-lean` is one-shot `ByteArray → Vector UInt8 32`; `hashes-fv` explicitly stripped RustCrypto's streaming `Digest` trait (`sha2/README.md:13`) to verify one-shot slices; `LeanSha256`, `btc-verified`, `lean-x509`, `LeanServer`, and even Lema's documented stdlib are one-shot. Proving arbitrary chunk-split invariance across a 64-byte partial-block buffer with zero-copy middle-block slicing is the flagship stateful problem in Appel (TOPLAS 2015) and HACL\* (`Hacl.Streaming.MD`). |
| **5. HMAC-SHA-256 (FIPS 198-1 / RFC 2104) proved from a SHA-256 spec** | **OPEN** in open-source Lean 4 (`proofbundle` is an empty stub; `SentinelOps` violates RFC 2104 for $>64$B keys; `Lema` repo is 404/closed) | **SELECT (Capstone Construction on top of #4).** In real cryptographic implementations, zero-copy `HMAC-SHA-256` *is* an instance of streaming SHA-256 initialized at a precomputed 1-block compressed inner/outer midstate (`istate`, `ostate`, initial byte count `64`), avoiding allocating `(K₀ ⊕ ipad) ++ message`. Proving a generalized prefix-state invariant for #4 discharges zero-copy streaming/one-shot `HMAC-SHA-256` against FIPS 198-1 with minimal extra machinery. |

**Chosen Target:** **Clean-room, `Apache-2.0`, zero-dependency (`Init`/`Std`-only on `leanprover/lean4:v4.34.1`) FIPS 180-4 & FIPS 198-1 Specification + Proved-Equivalent Incremental/Streaming SHA-256 (`init` / `update` / `finalize`) + Proved-Equivalent Zero-Copy Midstate/Streaming HMAC-SHA-256.**

---

### 2.2 Layer 1 — The Abstract Specification Layer (`Spec/`)

All definitions are written clean-room from public-domain NIST FIPS PUB 180-4 (`http://dx.doi.org/10.6028/NIST.FIPS.180-4`) and NIST FIPS PUB 198-1 (`https://doi.org/10.6028/NIST.FIPS.198-1`) using **only Lean 4 core (`Init` / `Std`, zero `Mathlib`, `set_option autoImplicit false`)**, purely functionally (no `Id.run do` mutable loops, avoiding the 3-file `forIn`/`MProd` desugaring tax seen in `fips-180-4-lean`):

1. **Words, rotations, constants, and round functions (`Spec/SHA256.lean`):**
   - Types: `abbrev Word := BitVec 32`, `abbrev Block := Vector Word 16`, `abbrev Schedule := Vector Word 64`, `abbrev State := Vector Word 8`, `abbrev Digest := BitVec 256`.
   - Word operations (§3.2, §4.1.2):
     - `rotr (n : Nat) (x : Word) : Word := x.rotateRight n`, `shr (n : Nat) (x : Word) : Word := x >>> n`, modular addition `+` on `BitVec 32`.
     - `ch x y z := (x &&& y) ^^^ (~~~x &&& z)`
     - `maj x y z := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)`
     - `bigSigma0 x := rotr 2 x ^^^ rotr 13 x ^^^ rotr 22 x`
     - `bigSigma1 x := rotr 6 x ^^^ rotr 11 x ^^^ rotr 25 x`
     - `smallSigma0 x := rotr 7 x ^^^ rotr 18 x ^^^ shr 3 x`
     - `smallSigma1 x := rotr 17 x ^^^ rotr 19 x ^^^ shr 10 x`
   - Constants: `K : Schedule` (64 literal `BitVec 32` hex words, §4.2.2) and `H0 : State` (8 literal `BitVec 32` hex words, §5.3.3).

2. **Pure functional schedule and compression (§6.2.2):**
   - `schedule (M : Block) : Schedule`: structural 48-step extension from `M.toArray` wrapped with its proved length invariant (or `Fin.foldl 48` over length-indexed `Vector Word (16 + t)`), paired with two immediate `simp` characterizations:
     - `schedule_lt_16 (M : Block) (t : Fin 64) (ht : t.val < 16) : (schedule M)[t] = M[t.val]'ht`
     - `schedule_ge_16 (M : Block) (t : Fin 64) (ht : 16 ≤ t.val) : (schedule M)[t] = smallSigma1 (schedule M)[t.val - 2] + (schedule M)[t.val - 7] + smallSigma0 (schedule M)[t.val - 15] + (schedule M)[t.val - 16]`
   - `round (W : Schedule) (s : State) (t : Fin 64) : State`: pure 8-word transition computing `T₁ = s[7] + bigSigma1 s[4] + ch s[4] s[5] s[6] + K[t] + W[t]` and `T₂ = bigSigma0 s[0] + maj s[0] s[1] s[2]`, returning `#v[T₁ + T₂, s[0], s[1], s[2], s[3] + T₁, s[4], s[5], s[6]]`.
   - `compress (H : State) (M : Block) : State := Vector.zipWith (· + ·) H (Fin.foldl 64 (round (schedule M)) H)`.

3. **Padding and parsing as proved mathematical constructions (`Spec/Padding.lean`):**
   - *Bit-level FIPS §5.1.1 padding:* For `M : List Bool` with `h : M.length < 2 ^ 64`, define `padZeros (ℓ : Nat) : Nat := (448 + 512 - (ℓ + 1) % 512) % 512` and `padBits (M : List Bool) : List Bool := M ++ [true] ++ List.replicate (padZeros M.length) false ++ bitVecToBitsBE (BitVec.ofNat 64 M.length)`.
   - *Proved structural properties of padding (part of the spec module, not left implicit):*
     - **Unique minimality (`padZeros_spec`):** `padZeros ℓ < 512 ∧ (ℓ + 1 + padZeros ℓ) % 512 = 448 ∧ ∀ k < padZeros ℓ, (ℓ + 1 + k) % 512 ≠ 448` — proving without `Mathlib.Data.Nat.Find` that the closed-form formula is the exact smallest non-negative solution to FIPS 180-4 §5.1.1's congruence $\ell + 1 + k \equiv 448 \pmod{512}$.
     - **Exact block divisibility (`padBits_length_dvd_512`):** `512 ∣ (padBits M).length` and `0 < (padBits M).length`, allowing **total, fallback-free block parsing** `parseBits (P : List Bool) (h : 512 ∣ P.length) : List Block` (eliminating `getD 0` junk fallbacks on partial blocks).
     - **Padding injectivity (`padBits_injective`):** For `M₁.length < 2^64` and `M₂.length < 2^64`, `padBits M₁ = padBits M₂ → M₁ = M₂` (extracting the last 64 bits recovers `Mᵢ.length`, and `List.take Mᵢ.length` recovers `Mᵢ`). This gives downstream Merkle–Damgård / Bitcoin / SSZ consumers true domain-separation theorems.
   - *Canonical byte-level corollary (`bytesToBits` & `padBytes`):* Define MSB-first `bytesToBits : List UInt8 → List Bool`, `sha256Bits (M : List Bool) (h : M.length < 2^64) : Digest`, and `sha256Bytes (m : List UInt8) (h : m.length < 2^61) : Vector UInt8 32`, with proved bijection `digestToBytesBE (sha256Bits (bytesToBits m) _) = sha256Bytes m h`.
   - *Prefix-aligned Merkle–Damgård split theorem (`sha256Bytes_prefix_blocks`):* Whenever `64 ∣ p.length` and `p.length + s.length < 2^61`, hashing `p ++ s` equals starting from midstate `(toBlocks p).foldl compress H0` and running tail padding on `s` with total bit-length `8 * (p.length + s.length)`.

4. **Abstract FIPS 198-1 / RFC 2104 HMAC Spec (`Spec/HMAC.lean`):**
   - Generic over block byte-size `B`, digest byte-size `L`, and hash `H : List UInt8 → List UInt8`, instantiated at `(64, 32, sha256SpecTotal)`:
     - `normalizeKey (K : List UInt8) : Vector UInt8 64`: if `K.length ≤ 64`, right-pad with `0x00` to 64 bytes; if `K.length > 64`, hash `H K` (32 bytes) and **right-pad with 32 `0x00` bytes to 64 bytes** (explicitly proving `(normalizeKey K).size = 64` in *both* branches, preventing the `SentinelOps` RFC-deviation bug).
     - `hmacSpec (K m : List UInt8) : Vector UInt8 32` defined verbatim per FIPS 198-1 §4 Table 1: $H((K_0 \oplus \texttt{0x5c}^{64}) \;\|\; H((K_0 \oplus \texttt{0x36}^{64}) \;\|\; m))$ under `K.length < 2^61` and `m.length + 64 < 2^61`.

---

### 2.3 Layer 2 — The Executable Implementation Layer (`Impl/`)

Designed for zero FFI, zero `panic!`, unboxed scalar codegen, and zero-copy slice absorption:

1. **Fast Block Engine (`Impl/Compress.lean`):**
   - `structure State32` (8 unboxed `UInt32` fields `h0..h7`) so Lean's C backend emits scalar `uint32_t` fields rather than boxed `Array UInt32` heap cells.
   - `UInt32` shift/or rotations `(x >>> n) ||| (x <<< (32 - n))` and big-endian `beU32At (bs : ByteArray) (off : Nat) (h : off + 4 ≤ bs.size) : UInt32` using bounds-checked `bs[off]'h` (no out-of-bounds `!` panics).
   - 16-word circular schedule + 64-round compression `compressSlice (st : State32) (bs : ByteArray) (off : Nat) (h : off + 64 ≤ bs.size) : State32` (plus `compressBlock64 (st : State32) (blk : Vector UInt8 64) : State32` for buffered/padded blocks).

2. **Incremental / Streaming State Machine (`Impl/Streaming.lean`):**
   ```lean
   structure Hasher where
     state      : State32
     buf        : ByteArray          -- invariant: buf.size < 64
     h_buf      : buf.size < 64
     totalBytes : UInt64             -- absorbed byte count (checked < 2^61)
     overflow   : Bool               -- latches true iff cumulative bytes ≥ 2^61
   ```
   - `Hasher.init : Hasher` (`state := H0_32, buf := ByteArray.empty, totalBytes := 0, overflow := false`).
   - `Hasher.update (ctx : Hasher) (chunk : ByteArray) : Hasher`:
     - Updates `(totalBytes', overflow')` with checked bound `< 2^61`.
     - **Path 1 (`ctx.buf.size + chunk.size < 64`):** `ctx.buf ++ chunk`, zero compressions.
     - **Path 2 (`ctx.buf.size = 0` and `chunk.size ≥ 64` — zero-copy fast path):** Runs `Nat.fold (chunk.size / 64)` calling `compressSlice` directly at `i * 64` inside `chunk` without copying `chunk`, then copies only the `< 64`-byte tail `chunk.extract (full * 64) chunk.size` into `buf`.
     - **Path 3 (`0 < ctx.buf.size < 64` and `ctx.buf.size + chunk.size ≥ 64` — boundary stitch):** Completes `ctx.buf` with `fill := 64 - ctx.buf.size` bytes from `chunk.extract 0 fill`, compresses that single 64-byte stitched block, runs `compressSlice` directly across the remaining `(chunk.size - fill) / 64` full blocks in `chunk`, and buffers the `< 64`-byte tail.
   - `Hasher.finalize (ctx : Hasher) : Vector UInt8 32` (and total `finalize? : Hasher → Option (Vector UInt8 32)` returning `none` iff `ctx.overflow`): constructs the 1-block (`ctx.buf.size < 56`) or 2-block (`56 ≤ ctx.buf.size < 64`) terminal FIPS §5.1.1 block(s) from `ctx.buf` and `ctx.totalBytes <<< 3`, compresses, and packs `State32` into `Vector UInt8 32`.
   - Derived zero-copy APIs:
     - `sha256 (bs : ByteArray) : Vector UInt8 32 := (Hasher.init.update bs).finalize`
     - `combine (a b : ByteArray) : Vector UInt8 32 := ((Hasher.init.update a).update b).finalize` (hashes `a` then `b` **without** allocating `a ++ b`, directly improving on `LeanSha256.combine`).

3. **Zero-Copy Midstate + Streaming `HMAC-SHA-256` (`Impl/HMAC.lean`):**
   - `PreparedKey` precomputes `istate : State32` (compressing the 64-byte `K₀ ⊕ ipad` block from `H0_32`) and `ostate : State32` (compressing `K₀ ⊕ opad` from `H0_32`) once per key.
   - `HmacHasher` wraps an inner `Hasher` seeded at `{ state := k.istate, buf := .empty, totalBytes := 64, overflow := false }` plus `ostate := k.ostate`.
   - `HmacHasher.update` delegates directly to `Hasher.update`; `HmacHasher.finalize` finalizes the inner `Hasher` to 32 bytes and runs a single 1-block final compression from `ostate` (32-byte payload `< 56`, total length `64 + 32 = 96` bytes $= 768$ bits). Never allocates `(K₀ ⊕ ipad) ++ m`.

---

### 2.4 Layer 3 — Equivalence-Proof Plan (`Equiv/`)

The entire proof architecture hinges on **one generalized simulation invariant** (`ModelsFrom`) parameterized by an initial state `iv : Spec.State` and a count `p : Nat` of already-compressed 64-byte prefix blocks (`p = 0, iv = Spec.H0` yields Streaming SHA-256; `p = 1, iv = Spec.compress Spec.H0 ipadBlk` yields Midstate Streaming HMAC-SHA-256 with zero duplicated loop proofs):

```lean
structure Hasher.ModelsFrom (iv : Spec.State) (p : Nat)
    (ctx : Impl.Hasher) (absorbed : List UInt8) : Prop where
  no_overflow : ctx.overflow = false
  len_bound   : p * 64 + absorbed.length < 2 ^ 61
  total_eq    : ctx.totalBytes.toNat = p * 64 + absorbed.length
  buf_eq      : ctx.buf.data.toList = absorbed.drop ((absorbed.length / 64) * 64)
  state_eq    : toSpecState ctx.state =
                  (parseExact64 (absorbed.take ((absorbed.length / 64) * 64))).foldl
                    Spec.compress iv
```

**Bridge lemma chain and where the hard proof obligations sit:**
1. **`Bridge/WordAndRound.lean` (Routine):** `UInt32.toBitVec` homomorphisms for `+`, `&&&`, `^^^`, `~~~`, `>>>`, `<<<`, shift/or `rotr`, `beU32At` ↔ `Word.ofBits` on 4-byte big-endian slices (proved by algebraic `BitVec` lemmas + 4-byte indexing, **zero `bv_decide`**).
2. **`Bridge/RingSchedule.lean` (Hard Step #1 — Medium):** Circular 16-word schedule invariant: after round $t \in [0, 64)$, slot `s % 16` holds `(Spec.schedule M)[s]` for every `s` in the active window `[max 0 (t - 16), t)` (for $t \ge 16$) and `M[s]` for `[t, 16)`. Proves `toSpecState (compressSlice st bs off h) = Spec.compress (toSpecState st) (sliceToSpecBlock bs off h)`.
3. **`Bridge/ChunkSplit.lean` & `Streaming/UpdateCorrect.lean` (Hard Step #2 — The Core Novelty):**
   - Pure list-chunking algebra lemma `split64_append (m c : List UInt8)`: relates `(m ++ c).take (((m.length + c.length) / 64) * 64)` and `.drop` to `m`'s prefix/remainder split across all three `Hasher.update` control-flow branches (`buf = 0` vs `0 < buf < 64`, and `< 64` vs `≥ 64`).
   - *Why this is the hardest step:* The boundary case where `0 < ctx.buf.size < 64` and `ctx.buf.size + chunk.size = 64 * k` (exact multiple, leaving empty tail buffer) vs `64 * k + r` requires clean modular arithmetic (`Nat.div_add_mod`, `List.take_append`, `List.drop_append`) so `fill = 64 - ctx.buf.size` never underflows or double-counts when `ctx.buf.size = 0` (handled by separating Path 2 and Path 3 explicitly in `Impl`).
   - Yields `Hasher.update_modelsFrom` and, by `List.foldl` induction over `chunks : List ByteArray`, `Hasher.foldl_update_modelsFrom`.
4. **`Streaming/FinalizeCorrect.lean` (Hard Step #3 — Medium):**
   - Connects `ctx.buf` (`= m.drop ((m.length / 64) * 64)`, length `< 64`) and `totalBits = 8 * (p * 64 + m.length)` across the 1-block (`buf.size < 56`) and 2-block (`56 ≤ buf.size < 64`) finalizers to `Spec.parseBits (Spec.padBits …)`.
   - Yields the headline streaming theorems (standard axioms `[propext, Classical.choice, Quot.sound]` only):
     ```lean
     theorem sha256_streaming_correct (chunks : List ByteArray)
         (h : (ByteArray.concat chunks).size < 2 ^ 61) :
         (chunks.foldl Hasher.update Hasher.init).finalize =
           Spec.sha256Bytes (ByteArray.concat chunks).data.toList h

     theorem sha256_chunk_invariant (c₁ c₂ : List ByteArray)
         (hEq : ByteArray.concat c₁ = ByteArray.concat c₂)
         (hLt : (ByteArray.concat c₁).size < 2 ^ 61) :
         (c₁.foldl Hasher.update Hasher.init).finalize =
           (c₂.foldl Hasher.update Hasher.init).finalize
     ```
     plus one-line corollaries `sha256_oneshot_correct` and `combine_eq_spec` (`combine a b = sha256 (a ++ b)` without allocating `a ++ b`).
5. **`Equiv/HMAC.lean` (Clean Payoff of `ModelsFrom`):**
   - Specializing `ModelsFrom` at `p = 1` and `iv = Spec.compress Spec.H0 (blockOf64 (ipadKey K₀))` immediately proves `HmacHasher.finalize (chunks.foldl HmacHasher.update (HmacHasher.init K)) = Spec.hmacSpec K.data.toList (ByteArray.concat chunks).data.toList` for all `K.size < 2^61` and `(ByteArray.concat chunks).size + 64 < 2^61`!

---

### 2.5 Test-Vector Source and Kernel-Checkable Validation (Zero `native_decide`)

1. **Authoritative vector sources:**
   - **NIST CSRC / CAVP Secure Hashing byte-oriented vectors** ([NIST CSRC CAVP Secure Hashing](https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/secure-hashing)):
     - `SHA256ShortMsg.rsp` (65 byte-aligned vectors of lengths `0, 8, 16, …, 512` bits = `0..64` bytes, exercising every mod-64 padding residue: empty `0`B, `"abc"` `3`B, max 1-block `55`B, min 2-block spill `56`B, `63`B, exact 1-block + pad-block `64`B).
     - `SHA256LongMsg.rsp` (64 multi-block vectors from `520` bits up to `129,024` bits = `16,128` bytes) and `SHA256Monte.rsp` (100 Monte Carlo checkpoints × 1,000 iterations).
   - **FIPS 180-4 Appendix B / NIST CSRC worked examples** (`""`, `"abc"`, 56-byte `"abcdbcde…nopq"`, 112-byte two-block example).
   - **IETF RFC 4231** ([RFC 4231 §4](https://datatracker.ietf.org/doc/html/rfc4231)): All **7 official HMAC-SHA-256 test vectors** (Cases 1–7, crucially including Case 6 & Case 7 with 131-byte keys $> 64$ bytes, testing over-long key hashing + 32-byte zero-padding).
   - **Adversarial chunk-partition vectors:** Splitting 0B, 55B, 56B, 64B, 128B, and 1,000B inputs across `[0]`, 1-byte drips, `[55, 1]`, `[63, 1]`, `[64, 0, 64]`, and uneven prime-sized chunks.

2. **How to check vectors inside the Lean kernel WITHOUT `native_decide` (`Lean.ofReduceBool` banned):**
   - **Why naive kernel `decide` stalls on `ByteArray` / `Vector (BitVec 32)`:** Inside Lean 4's C++ trusted kernel (`whnf`), `ByteArray` and `Array` are not backed by flat C buffers — they reduce as linked `List` structures, and `Fin`-indexed `Vector` operations carry arithmetic proof terms (`omega`) that can explode during WHNF unfolding. By contrast, Lean's C++ kernel accelerates `Nat` arithmetic and bitwise primitives (`Nat.add`, `Nat.land`, `Nat.lor`, `Nat.xor`, `Nat.shiftLeft`, `Nat.shiftRight`) natively via GMP. Primary-source inspection of `keithadler/lean-x509` ([`X509/Sha256.lean`](https://raw.githubusercontent.com/keithadler/lean-x509/main/X509/Sha256.lean) and [`X509/Real.lean`](https://raw.githubusercontent.com/keithadler/lean-x509/main/X509/Real.lean)) confirms that a ~100-line `Nat`-word SHA-256 evaluator executes ~190+ block compressions inside **`by decide +kernel`** on `v4.34+` in seconds with **zero compiler-trust axioms** (`test/Axioms.lean`).
   - **Two-tier, zero-`native_decide` verification harness:**
     1. **Kernel-checked KAT theorem suite (`Tests/KernelVectors.lean`, closed strictly by `decide +kernel` + proved `rw`, zero `Lean.ofReduceBool`):**
        Include a compact ~80-line GMP-friendly `Nat`-word evaluator `KernelEval.sha256Nat : List Nat → Nat` (flat 8-field `Nat` struct, no `Array`/`Fin` proof terms), prove `Spec.sha256Bytes_eq_sha256Nat` once under standard axioms, and prove as **actual kernel-checked Lean `theorem`s**:
        - All **65 `SHA256ShortMsg.rsp` byte-oriented vectors (`0..64` bytes)** + FIPS §B anchor vectors + selected multi-KB `SHA256LongMsg.rsp` vectors, transported by `rw [sha256_streaming_correct, Spec.sha256Bytes_eq_sha256Nat]` and closed by `decide +kernel`;
        - All **7 RFC 4231 HMAC-SHA-256 test vectors (Cases 1–7)** on both `Spec.hmacSpec` and `Impl.HmacHasher`, closed via `decide +kernel`;
        - Concrete streaming chunk-partition `theorem`s.
        Every KAT theorem is audited in `AxiomAudit.lean` to confirm `#print axioms` contains **only a subset of `[propext, Classical.choice, Quot.sound]`** (never `Lean.ofReduceBool` or `sorryAx`).
     2. **Full CAVP + Monte Carlo runtime test executable (`lake exe cavp-suite`):**
        Run the complete 129-case `ShortMsg` + `LongMsg` suite and the 100,000-compression `SHA256Monte.rsp` suite in a standalone `IO` binary (`Main.lean` returning exit code `0` iff all vectors pass) during CI — never via `native_decide` inside library or test `.olean`s.

---

## 3. Milestone Decomposition

All milestones target a standalone package on the programme's pinned toolchain (`leanprover/lean4:v4.34.1`), **zero external dependencies** (`Init` / `Std` only — no `Mathlib`, no `mdgen`, no FFI), licensed `Apache-2.0`. Every milestone must leave `lake build` green with **zero `sorry`s, zero `admit`s, zero `native_decide`, zero `bv_decide`**, and pass compile-time `#guard_msgs in #print axioms` checks showing only subsets of `[propext, Classical.choice, Quot.sound]`.

### Dependency Order & Parallelism Map

```text
                       ┌──► M2: Nat Kernel Evaluator + Spec KATs (65 CAVP + 7 RFC 4231) ──────────┐
                       │    [Independent of M3 & M4]                                              │
M1: FIPS 180-4 & 198-1─┤                                                                          ├──► M6: Streaming KATs,
    Pure Spec + Pad    │                                       ┌──► M5: Midstate/Streaming HMAC ──┤        CAVP Monte Runner
    Theorems           └──► M3: Scalar Compress + Ring-Buffer ─┴──► M4: Streaming Hasher          │        & Global Axiom Gate
                            Equiv [Parallel with M2]                (init/update/finalize) ───────┘
```

- **Parallel Wave 1 (after `M1`):** `M2` and `M3` touch disjoint directories (`KernelEval/` + `Tests/SpecKAT.lean` vs. `Impl/Compress.lean` + `Equiv/Compress.lean`) and can run concurrently on two lanes; `M2` also stays independent of `M4`.
- **Parallel Wave 2 (after `M4`):** `M5` (`Impl/HMAC.lean` + `Equiv/HMAC.lean`) and `M6`'s streaming test/CAVP harness (`Tests/StreamingKAT.lean` + `Tests/CavpRunner.lean`) are independent and can run concurrently before the final root `AxiomAudit.lean` gate imports both.

---

### Milestone Specifications (Single-Lane Sized)

#### M1 — Clean-Room FIPS 180-4 & FIPS 198-1 Pure Functional Spec + Proved Padding (`Spec/`)
- **Dependencies:** None (root milestone).
- **Scope:** Author the standalone, human-readable mathematical specifications of SHA-256 (FIPS 180-4 §§3–6.2) and HMAC-SHA-256 (FIPS 198-1 / RFC 2104) over `BitVec 32`, `Vector`, `List Bool`, and `List UInt8` with `set_option autoImplicit false` and zero imperative `Id.run do` blocks. Prove the mathematical properties of FIPS §5.1.1 padding and Merkle–Damgård aligned-block splitting directly in the spec package. Perform independent second-model English back-translation fidelity check on every definition against NIST FIPS 180-4 / 198-1 text.
- **Deliverable:**
  - `Spec/SHA256.lean`: `Word`, `Block`, `Schedule`, `State`, `Digest`, `ch`, `maj`, `bigSigma0`, `bigSigma1`, `smallSigma0`, `smallSigma1`, `K`, `H0`, `schedule` (+ `schedule_lt_16`, `schedule_ge_16`), `round`, `compress`.
  - `Spec/Padding.lean`: `padZeros`, `padBits`, `parseBits`, `sha256Bits`, `bytesToBits`, `sha256Bytes`; theorems `padZeros_spec` (unique minimal mod-512 solution), `padBits_length_dvd_512`, `padBits_injective` (domain separation), `digestToBytesBE_sha256Bits_eq_sha256Bytes`, and `sha256Bytes_prefix_blocks` (aligned 64-byte prefix midstate decomposition).
  - `Spec/HMAC.lean`: `normalizeKey` (+ `normalizeKey_size : (normalizeKey K).size = 64`), `hmacSpec`, `hmacSpec_congr`.
- **Acceptance evidence (kernel bar):** `lake build Spec` exits `0`; zero `sorry`s; `#guard_msgs in #print axioms` on `padZeros_spec`, `padBits_length_dvd_512`, `padBits_injective`, `sha256Bytes_prefix_blocks`, and `normalizeKey_size` shows $\subseteq \{\texttt{propext}, \texttt{Classical.choice}, \texttt{Quot.sound}\}$.

#### M2 — GMP `Nat`-Word Kernel Evaluator & Spec-Level Kernel KAT Suite (`KernelEval/`, `Tests/SpecKAT.lean`)
- **Dependencies:** `M1` only *(runs in parallel with `M3` and `M4`)*.
- **Scope:** Implement a compact (~80 LOC) proof-term-free `Nat`-word SHA-256 evaluator (`KernelEval.sha256Nat`) optimized for Lean's C++ GMP kernel reducer, prove `Spec.sha256Bytes_eq_sha256Nat`, and lock `M1`'s definitions against official NIST and IETF test vectors inside the Lean kernel using `decide +kernel` (strictly zero `native_decide`).
- **Deliverable:**
  - `KernelEval/SHA256Nat.lean`: `sha256Nat : List Nat → Nat` and bridge theorem `Spec.sha256Bytes_eq_sha256Nat`.
  - `Tests/SpecKAT.lean`: Kernel-checked `theorem`s closed via `decide +kernel` + `Spec.sha256Bytes_eq_sha256Nat` for: (a) all 3 FIPS 180-4 §B examples, (b) all **65 byte-oriented vectors (`0..64` bytes) from NIST CAVP `SHA256ShortMsg.rsp`**, (c) selected multi-block `SHA256LongMsg.rsp` vectors, and (d) all **7 RFC 4231 HMAC-SHA-256 test cases** (Cases 1–7, including 131-byte over-long keys).
- **Acceptance evidence (kernel bar):** `lake build KernelEval Tests.SpecKAT` exits `0`; zero `sorry`s; `#guard_msgs in #print axioms` on `sha256Bytes_eq_sha256Nat` and representative `SpecKAT` theorems confirms `Lean.ofReduceBool` is **absent** (standard three axioms or `[]` only).

#### M3 — Unboxed Scalar Block Compression & 16-Word Ring-Buffer Equivalence (`Impl/Compress.lean`, `Equiv/Compress.lean`)
- **Dependencies:** `M1` only *(runs in parallel with `M2`)*.
- **Scope:** Implement the executable `UInt32` compression core (`State32` scalar struct, shift/or `UInt32` rotations, bounds-checked big-endian slice decoding `beU32At`, 16-word circular ring-buffer schedule, `compressSlice` and `compressBlock64`) and prove per-block equivalence against `Spec.compress` using pure `BitVec` / modular index arithmetic (**no `bv_decide`**).
- **Deliverable:**
  - `Impl/Compress.lean`: `State32`, `H0_32`, `K32`, `beU32At`, `compressSlice`, `compressBlock64`.
  - `Equiv/Compress.lean`: `toSpecState`, `sliceToSpecBlock`, `block64ToSpecBlock`, ring-buffer schedule window invariant, and headline theorems `compressSlice_eq_spec` and `compressBlock64_eq_spec`.
- **Acceptance evidence (kernel bar):** `lake build Impl.Compress Equiv.Compress` exits `0`; zero `sorry`s; `#guard_msgs in #print axioms` on `compressSlice_eq_spec` and `compressBlock64_eq_spec` shows $\subseteq \{\texttt{propext}, \texttt{Classical.choice}, \texttt{Quot.sound}\}$.

#### M4 — Streaming `Hasher` (`init`/`update`/`finalize`) & Chunk-Invariance Proof (`Impl/Streaming.lean`, `Equiv/Streaming.lean`)
- **Dependencies:** `M1`, `M3`.
- **Scope:** Implement the stateful incremental `Hasher` (`init`, 3-path zero-copy `update`, overflow-checked `finalize?` / `finalize`, plus zero-copy `sha256` and `combine`), define the prefix-parameterized simulation invariant `Hasher.ModelsFrom iv p ctx absorbed`, prove preservation across `update` (all 3 buffer/boundary paths) and `List.foldl`, and prove `finalize` agreement with `Spec.sha256Bytes`.
- **Deliverable:**
  - `Impl/Streaming.lean`: `Hasher`, `Hasher.init`, `Hasher.update`, `Hasher.finalize`, `Hasher.finalize?`, `Impl.sha256`, `Impl.combine`.
  - `Equiv/Streaming.lean`: `Hasher.ModelsFrom`, `update_modelsFrom`, `foldl_update_modelsFrom`, `finalize_modelsFrom_eq_spec`, and public theorems `sha256_streaming_correct`, `sha256_chunk_invariant`, `sha256_oneshot_correct`, and `combine_eq_spec`.
- **Acceptance evidence (kernel bar):** `lake build Impl.Streaming Equiv.Streaming` exits `0`; zero `sorry`s; `#guard_msgs in #print axioms` on `sha256_streaming_correct`, `sha256_chunk_invariant`, `sha256_oneshot_correct`, and `combine_eq_spec` shows $\subseteq \{\texttt{propext}, \texttt{Classical.choice}, \texttt{Quot.sound}\}$.

#### M5 — Zero-Copy Midstate & Streaming `HMAC-SHA-256` + FIPS 198-1 Equivalence (`Impl/HMAC.lean`, `Equiv/HMAC.lean`)
- **Dependencies:** `M1`, `M4` *(runs in parallel with `M6` harness work)*.
- **Scope:** Implement reusable key preparation (`PreparedKey` precomputing 1-block compressed `istate` and `ostate`) and streaming/one-shot `HmacHasher` (`init`, `update`, `finalize`, `hmacSha256`) that never allocates `(K₀ ⊕ ipad) ++ message`. Instantiate `M4`'s `ModelsFrom` at `p = 1` (`64` prefix bytes) to prove equivalence to `Spec.hmacSpec` for both chunked and one-shot messages across all key lengths (`≤ 64`B and `> 64`B).
- **Deliverable:**
  - `Impl/HMAC.lean`: `PreparedKey`, `PreparedKey.ofKey`, `HmacHasher`, `HmacHasher.init`, `HmacHasher.update`, `HmacHasher.finalize`, `Impl.hmacSha256`.
  - `Equiv/HMAC.lean`: `hmac_streaming_correct` and `hmac_oneshot_correct`.
- **Acceptance evidence (kernel bar):** `lake build Impl.HMAC Equiv.HMAC` exits `0`; zero `sorry`s; `#guard_msgs in #print axioms` on `hmac_streaming_correct` and `hmac_oneshot_correct` shows $\subseteq \{\texttt{propext}, \texttt{Classical.choice}, \texttt{Quot.sound}\}$.

#### M6 — Streaming Kernel KATs, Full CAVP Runtime Runner & Whole-Repo Axiom Audit (`Tests/`, `AxiomAudit.lean`)
- **Dependencies:** `M2`, `M4`, `M5`.
- **Scope:** Transport `M2`'s kernel-checked CAVP and RFC 4231 theorems onto `Impl.Hasher` and `Impl.HmacHasher` across adversarial chunk splits (`[0]`, 1-byte drips, `[55, 1]`, `[63, 1]`, `[64, 0, 64]`), add a standalone `IO` runner (`lake exe cavp-suite`) executing all 129 NIST `ShortMsg` + `LongMsg` vectors plus all 100×1,000 `SHA256Monte.rsp` Monte Carlo iterations and randomized chunk-split differential tests, and add an automated metaprogramming `AxiomAudit.lean` gate walking `env.constants` (`collectAxioms`) across every non-internal declaration in the package.
- **Deliverable:**
  - `Tests/StreamingKAT.lean` (kernel-checked via `decide +kernel` + `Equiv` rewrites, zero `native_decide`),
  - `Tests/CavpRunner.lean` (`lake_exe cavp-suite` parsing unmodified NIST `.rsp` files),
  - `AxiomAudit.lean` (`#guard_msgs` pins on all headline theorems + environment-wide `collectAxioms` assertion rejecting `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, or any custom axiom).
- **Acceptance evidence (kernel bar):** `lake build` and `lake exe cavp-suite` both exit `0`; `AxiomAudit.lean` logs 100% compliance across all package declarations (`⊆ [propext, Classical.choice, Quot.sound]`, zero `sorry`s); hostile cross-pool review passes.

---

## 4. Risks and Open Questions

### 4.1 Risks That Could Kill, Shrink, or Complicate the Target

1. **Upstream movement in `remix7531/fips-180-4-lean` or `remix7531/hashes-fv`:**
   Today, neither repository covers streaming (`init`/`update`/`finalize`) or HMAC — `fips-180-4-lean` is strictly one-shot, and `hashes-fv` explicitly deleted RustCrypto's `digest::Digest` streaming API to make verification tractable (`sha2/README.md:13`). Both SHA-2 repos have been untouched since May 26–28, 2026 (~5 months dormant), though `remix7531` remains active on GitHub across other projects (`rocq`, `nixpkgs`, `silktouch` pushed 2026-10-26). If `remix7531` resumes SHA-2 work to add `BlockBuffer` streaming or `FIPS 198-1` HMAC, mathematical novelty narrows (though `GPL-3.0-or-later` and `Mathlib` coupling would still block permissive zero-dependency consumers). **Mitigation:** Re-check `remix7531`'s public repos immediately prior to launching `M1`.
2. **Potential open-sourcing of Lema's standard library (`LorenaLabs/lema-lang`):**
   Lema's public documentation (`lema-lang.org/docs/reference/standard-library/`, updated 2026-10-26) claims checked one-shot `Sha256Unboxed` and one-shot `Hmac` (`Std.Crypto.Hmac`) inside Lema's content-addressed object store (`lema.core/v3`). Even if LorenaLabs later publishes that store, (a) Lema's documented APIs are **one-shot** (`digestSlice`, `hmacSha256`) rather than an incremental `init`/`update`/`finalize` streaming state machine, and (b) Lema retired standalone Lake `.lean` library files in favor of its custom language/store toolchain (Decision `0038`). Still, public release of Lema's Lean objects would shrink one-shot HMAC novelty while leaving streaming SHA-256 + zero-copy midstate streaming HMAC open.
3. **Overlap / duplication perception on `M1` & `M3` vs. `remix7531/fips-180-4-lean`:**
   Milestones `M1` (FIPS 180-4 spec) and `M3` (scalar compression + ring-buffer schedule proof) account for roughly 35–40% of the build effort and cover mathematical ground already proved in `fips-180-4-lean`. Why not `require «fips-pub-180-4»` directly? Three hard blockers prevent importing it: (i) its **`GPL-3.0-or-later` license** (`LICENSE`) legally taints any importing Lean library (`hashes-fv`'s proofs had to adopt `GPL-3.0-or-later` for this exact reason); (ii) it pins `leanprover/lean4:v4.29.1` (five minor versions behind the programme's `v4.34.1`) and pulls in full `Mathlib` + `mdgen` inside `spec/`; and (iii) clean-room authorship directly from public-domain NIST FIPS 180-4 / 198-1 is mandatory to stay free of GPL derivative-work claims. **Decision gate for programme leadership:** If re-proving block compression clean-room as the `Apache-2.0`, zero-Mathlib foundation for `M4` (Streaming) + `M5` (Midstate HMAC) is judged too much overlap for current lane priority, the entire SHA-256 cluster should stay closed in favor of completely uncrowded Software-shelf targets (e.g., the UTF-8 Table 3-7 bridge).
4. **Silent `Lean.ofReduceBool` contamination via `bv_decide`:**
   In Lean 4 (`Std.Tactic.BVDecide`), `bv_decide` verifies LRAT certificates via `native_decide`, injecting `Lean.ofReduceBool` into `#print axioms` and violating the programme's three-axiom bar (`[propext, Classical.choice, Quot.sound]`). **Mitigation:** Explicitly forbid both `native_decide` and `bv_decide` in all lane prompts; prove the six `UInt32 ↔ BitVec 32` operator bridges in `M3` via core algebraic lemmas (`UInt32.toBitVec`, shift/or bit-extensionality), as `fips-180-4-lean` (`equiv/SHA256/Bridge.lean`) demonstrated is cleanly doable.
5. **Kernel WHNF memory/heartbeat limits if oversized vectors are fed to `decide +kernel`:**
   While `keithadler/lean-x509` (`X509/Real.lean`) proves ~190+ SHA-256 block compressions in seconds via `decide +kernel` over `Nat` words, attempting `decide +kernel` on 16 KB `SHA256LongMsg.rsp` entries or 100,000-iteration `SHA256Monte.rsp` loops will exhaust kernel memory/heartbeats. **Mitigation:** Restrict `decide +kernel` theorems in `M2`/`M6` to the ~75 high-signal boundary/RFC cases (`0..64`B `ShortMsg`, FIPS §B, selected multi-block cases $\le 1\text{–}2$ KB, all 7 RFC 4231 cases, and chunk-split tests), and run the full 129-case + 100k-block Monte Carlo suites in `M6`'s compiled `lake exe cavp-suite` binary.

---

### 4.2 Unresolved Questions (Listed Plainly)

1. **Source-level audit of `LorenaLabs/lema-lang` (`UNVERIFIED`):** `https://github.com/LorenaLabs/lema-lang.git` (referenced in `lema-lang.org/docs/tutorials/set-up/`) returned `HTTP 404 Not Found` on 2026-10-26. We could not inspect the exact Lean definitions, theorem statements, preconditions, or axiom footprints of `Sha256Spec`, `Sha256Unboxed`, or `Std.Crypto.Hmac`, nor verify whether LorenaLabs plans a public release.
2. **End-to-end Lean proof replay of `remix7531/hashes-fv` (`sha2-fv`) (`UNVERIFIED`):** Although all 35 hand-written `.lean` files in `hashes-fv` contain zero `sorry`s, `Extraction/{Funs,Types}.lean` are absent from both the GitHub tree and `sha2-fv-0.1.0.crate`, GitHub Actions (`sha2.yml`) runs Cargo tests only, and research-only rules precluded running Nix + Charon + Aeneas locally. Whether `make extract && make prove` currently builds cleanly against `fips-180-4-lean @ main` and outputs the exact four axioms claimed in `sha2/README.md` could not be machine-checked here.
3. **Migration effort of `fips-180-4-lean` from `v4.29.1` to `v4.34.1`:** Because we did not clone or run `lake build` locally, the exact amount of Lean/Mathlib API breakage across five minor releases (`v4.29.1 → v4.34.1`) is unmeasured (and moot if clean-room `Apache-2.0` authorship is required anyway).
4. **Closed industrial Lean 4 repositories:** Private corpora (e.g., Meta ATLAS, internal Cryspen/AWS/Lean FRO branches) are invisible to public web/GitHub search; we cannot rule out unpublished internal streaming SHA-256 or HMAC developments.
5. **Functional equivalence vs. game-based PRF security for `HMAC-SHA-256`:** Milestone `M5` proves functional equivalence of zero-copy midstate/streaming `HMAC-SHA-256` to FIPS 198-1 (`Spec.hmacSpec`). Whether a later cryptography-shelf ticket should also formalize Bellare's NMAC/HMAC PRF reduction (as Beringer et al. 2015 did in Coq/FCF, using `VCV-io` or `CatCrypt` in Lean 4) is an open programme-scope question.

---

### What This Dossier Does NOT Show

This dossier is based strictly on read-only primary-source inspection (GitHub API, raw repository files, crates.io tarballs, CI run logs, and published documentation/papers) conducted on 2026-10-26; **no repository was cloned or compiled locally with `lake build`**. Consequently, kernel acceptance of `remix7531/fips-180-4-lean` rests on source inspection of all 57 `.lean` files (`equiv/AxiomCheck.lean` `#guard_msgs`) paired with its public GitHub Actions success log (`actions/runs/26441432411`), while Lean compilation of `remix7531/hashes-fv` (`sha2-fv`) and all source claims from `lema-lang.org` (`LorenaLabs/lema-lang` HTTP 404) remain explicitly marked `UNVERIFIED` at the machine-replay / source level respectively. Furthermore, the proposed specification and equivalence architecture proves **pure Lean source-level functional correctness** against NIST FIPS 180-4 and FIPS 198-1 under Lean's three standard axioms; it does **not** prove cryptographic collision resistance or unforgeability, does **not** verify Lean's C code generator, C compiler, or runtime memory model, and does **not** establish hardware/microarchitectural constant-time guarantees.

DOSSIER COMPLETE
