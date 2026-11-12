# Prior-art pass: SHA-256 (FIPS 180-4) as a Lean 4 formalization target

Date: 2026-10-26. Method: multiple web searches (general web + GitHub/lib.rs/ethresear.ch),
with the strongest hits opened and read. Adversarial stance throughout: the goal was to
*find* existing work, not to confirm a gap.

## Headline verdicts

**LEAN STATUS: PARTIAL**

**ATTENTION: HIGH overall / LOW–MEDIUM Lean-specific**

Overall attention is not in doubt: SHA-256 is arguably the most-verified cryptographic
primitive in existence outside Lean (see the non-Lean table). Lean-specific attention is
real but recent, small-team, and niche: one specification-grade pure-Lean implementation
with test-vector validation and conformance lemmas (LeanSha256, inside the Etheorem
Ethereum project), one crates.io crate claiming full Lean 4 correctness proofs for a Rust
SHA-2 implementation (sha2-fv, repository not inspectable from search results), one Lean
circuit arithmetization of the compression function for ZK use (Freigen), and adjacent
Lean work that assumes or abstracts SHA-256 rather than formalizing it (SizzLean's FFI
axioms, LNSym's SHA-512 — not SHA-256 — ARM verification, CatCrypt's translated specs).
No SHA-256 exists in Lean core, Mathlib, or Batteries (searches for one returned nothing).

## Why PARTIAL and not CLEAN or TAKEN

What exists in Lean today, precisely:

1. **LeanSha256 is an implementation-as-specification, not a spec + proved implementation.**
   It is a pure, kernel-reducible Lean definition of SHA-256 (`hash`, `combine`), with
   *no separate, independently stated FIPS 180-4 specification* against which an
   equivalence theorem is proved. Its correctness evidence is: (a) NIST CAVP byte-oriented
   short/long-message suites passing as build-time `native_decide` gates (129 cases,
   ~108 s; note `native_decide` adds the `Lean.ofReduceBool` compiler-trust axiom in the
   *test* library), (b) three anchor FIPS 180-4 §B example gates in the core library, and
   (c) "a handful of structural conformance lemmas" (e.g. `hash` agrees with a single-block
   compression on inputs ≤ 55 bytes). The ethresear.ch announcement describes this as
   "the compression function and the message schedule proved against the FIPS 180-4
   specification"; the package's own README is more modest and is the more reliable
   source — it claims CAVP validation and structural lemmas, not a spec-equivalence proof.
   The README also states: no `sorry`, no `axiom` declarations, no FFI anywhere in the
   library (project claim, taken from the README, not independently re-audited here).
2. **The fast/native path in its main consumer is axiomatized, by design.** SizzLean
   (the SSZ library built on LeanSha256) connects its OpenSSL FFI hasher to the pure spec
   via three named axioms — `sha256Hash_eq_spec`, `sha256Combine_eq_spec`,
   `sha256BatchCombine_eq_spec` — and the authors explicitly note each could later be
   replaced by a proved theorem. So "native implementation proved equal to the Lean spec"
   is an open, named gap in the existing Lean ecosystem, not a solved problem.
3. **sha2-fv's claim, if it holds, covers a different artifact than a standalone Lean
   formalization.** The lib.rs/crates.io listing (v0.1.0) describes "Formally verified
   Pure Rust implementation of the SHA-2 hash function family (SHA-224, SHA-256, SHA-384,
   SHA-512, SHA-512/224, SHA-512/256), with Lean 4 proofs of correctness against
   FIPS 180-4." That is a Rust implementation with Lean proofs (a Verus/Aeneas-style
   arrangement), covering the whole family including SHA-224. I could not surface its
   repository from search results to audit sorries, the exact theorem statements, or
   activity, so this entry is **listing-grade evidence only** — it must be inspected
   directly before anyone relies on the classification either way.
4. **Scope gaps in what is solidly established:** LeanSha256 covers SHA-256 only (no
   SHA-224), is one-shot `ByteArray → ByteArray` (no streaming/init-update-final API
   proved equivalent), and there is no Lean treatment of HMAC-SHA-256 as a construction
   proved from the SHA-256 spec.

So the narrow claim "a pure-Lean executable SHA-256 exists and passes CAVP" is TAKEN.
The broader claim "SHA-256 is formalized in Lean at the programme's kernel bar — an
independently readable FIPS 180-4 specification, a proved equivalence for an efficient
implementation, standard axioms only" is NOT taken. Hence PARTIAL.

## Per-source table

| Name | URL | System | What exists | Completeness |
|---|---|---|---|---|
| LeanSha256 (Etheorem) | https://github.com/etheorem/etheorem/blob/main/packages/LeanSha256 (mirror: https://github.com/etheorem/LeanSha256) | Lean 4 | Pure-Lean, kernel-reducible SHA-256 (`hash`, `combine`); initial state, message schedule, compression, padding, multi-block driver in `LeanSha256.Core`; v0.1.0, "Stable", LGPL-3.0, Reservoir-indexed; no Mathlib/Batteries deps | CAVP short+long suites pass via `native_decide` test gates; 3 FIPS §B anchor gates in core; a handful of structural conformance lemmas; README claims no sorry/axiom/FFI in the library. Implementation-as-spec: no independent FIPS spec + equivalence theorem; SHA-256 only; one-shot API |
| SizzLean (Etheorem) | https://github.com/etheorem/etheorem/tree/main/packages/SizzLean ; announcement https://ethresear.ch/t/lean4-ssz-library-formally-verified-and-easy-to-use/25988 | Lean 4 | Verified SSZ library whose Merkleization is generic over a hash function; uses LeanSha256 as its pure spec instance | SHA-256 itself is *assumed*, not proved, on the fast path: 3 axioms equate the OpenSSL FFI hasher to the pure spec; central SSZ theorems otherwise carry only the 3 standard kernel axioms. Direct evidence that the native↔spec bridge is an acknowledged open gap |
| Etheorem consensus specs | https://ethresear.ch/t/etheorem-update-the-complete-executable-consensus-specs-written-in-lean-4/26063 | Lean 4 | Full executable Ethereum consensus specs (Fulu/Gloas/Heze) in Lean, two modes: fast (FFI SHA-256) and pure (kernel-reducible SHA-256) | Uses SHA-256 as a primitive component; not itself a SHA-256 formalization |
| sha2-fv | http://lib.rs/keywords/sha-2 (listing; also https://lib.rs/cryptography) | Rust + Lean 4 proofs | crates.io crate v0.1.0: pure Rust, no-std/no-alloc SHA-2 family (224/256/384/512/512/224/512/256), "Lean 4 proofs of correctness against FIPS 180-4" | **Unverified beyond the listing.** Repository, theorem statements, sorry count, and activity could not be surfaced from search; inspect before relying on it |
| LNSym (leanprover) | https://deepwiki.com/leanprover/LNSym/6-verification-applications | Lean 4 | Symbolic simulator for ARMv8; formally verified ARM assembly for **SHA-512** (`Proofs/SHA512/`, `Tests/SHA2/SHA512ProgramTest.lean`) | Adjacent only: SHA-512 at assembly level; no SHA-256 program proof found. Shows the "efficient implementation" end of the spectrum exists in Lean for the sibling algorithm |
| Freigen / BitZ arithmetization | http://eprint.iacr.asia/2026/2141.pdf | Lean 4 | Full arithmetization of SHA-256 compression as a circuit relation (`Freigen/Circuit/Examples/Sha256.lean`), 7,144-bit witness per compression, benchmarked against Binius64/Flock and an AI-found arithmetization from the zkGolf competition | A circuit/constraint formalization of the compression function for ZK proving — a real Lean formalization of the compression math, but aimed at witness size, not FIPS-spec equivalence of a hash implementation |
| CatCrypt | http://eprint.iacr.asia/2026/604.pdf | Lean 4 (+ F*/Vale via libcrux/hax) | Protocol security proofs in Lean (HPKE, EDHOC, SPQR); HKDF-SHA256 used as a PRF assumption, optionally instantiated from verified libcrux primitives | SHA-256 is an assumption/bridge, with primitive specs *translated* from F*/Vale and validated by test vectors — not a Lean formalization of SHA-256 itself |
| Appel, "Verification of a Cryptographic Primitive: SHA-256" (TOPLAS 2015) | https://agc.asuis.workers.dev/read-https-www.cs.princeton.edu/~appel/papers/verif-sha-2.pdf | Coq + VST + CompCert | The canonical full formalization: FIPS 180-4 functional spec in Coq, OpenSSL's C SHA-256 (init/update/final) proved functionally correct and memory-safe against it, ~9,000 lines of Coq | Complete for its artifact; the two-level spec/impl architecture Lean still lacks. Attention anchor for the whole area |
| HACL* / HACL | https://css.csail.mit.edu/6.5660/2024/readings/hacl-star.pdf | F* (+ Vale for asm) | SHA-256 (and SHA-512) written in Low*, proved functionally correct vs a pure F* spec, memory-safe and secret-independent, compiled to C; ~708 lines total for SHA-256 vs Appel's ~9,000; ships in Firefox, the Linux kernel, and (since Python 3.14) CPython's hashlib fallback | Complete and deployed at massive scale. Overall-attention evidence, not Lean |
| SAW / Cryptol verified crypto (Galois, AWS) | https://link.springer.com/content/pdf/10.1007/978-3-030-81685-8_31.pdf | Cryptol + SAW | Machine-assisted proofs that AWS-LibCrypto (BoringSSL-lineage) C/x86 implementations are I/O-equivalent to algorithmic specs — AES-256-GCM and SHA-384 in that paper; earlier SAW work verified HMAC-SHA-256 C code against a Cryptol spec | Complete for the verified artifacts; equivalence-checking methodology rather than a spec library |
| Python hashlib docs (HACL* note) | https://docs.python.org/sv/3.15/library/hashlib.html | F* (via HACL*) | Documents that hashlib falls back to HACL* verified implementations, including SHA-256 | Deployment evidence for the F* line, included because it shows how far the non-Lean verified SHA-256 ecosystem has propagated |

Negative results (searched, nothing found): SHA-256 in Lean core / Mathlib / Batteries;
any Lean formalization of HMAC-SHA-256 proved from a SHA-256 spec; any Lean SHA-224;
any peer-reviewed paper devoted to SHA-256 in Lean (the Lean work above is announced in
forum posts — two ethresear.ch threads — and package listings, not papers).

## Attention assessment

- **Overall: HIGH.** SHA-256 verification is a 15-year, multi-system literature: Appel's
  Coq/VST verification of OpenSSL (TOPLAS 2015, with a maintained second edition),
  HACL*'s F* verification deployed in Firefox/Linux/CPython, Galois/AWS SAW proofs over
  BoringSSL-lineage code, Vale/EverCrypt verified assembly, plus textbook status
  (SHA-256 is the running example in software-verification courses, e.g. the VST course
  materials). Anyone claiming SHA-256 verification is "neglected" in general would be
  repeating the Prove2Me mistake at larger scale.
- **Lean-specific: LOW–MEDIUM.** All Lean artifacts found are from 2025–2026, produced by
  small teams (Etheorem: seven contributors, Ethereum Protocol Fellowship / Invisible
  Garden orbit), announced on ethresear.ch rather than in venues, and consumed mainly by
  the Lean-Ethereum ecosystem. LeanSha256 is packaged properly (versioned v0.1.0,
  Reservoir-indexed, subtree mirror) but is a component of a larger project, not a
  standalone, widely-cited formalization. sha2-fv is a single v0.1.0 crate with no visible
  footprint beyond its listing. There is no Lean SHA-256 paper trail comparable to the
  Coq/F* one.

## Bottom line: what a complete Lean formalization would still add

A new Lean effort would not be duplicating Appel or HACL*, and would only partially
overlap LeanSha256: what is still missing in Lean is the *two-level* artifact those
older systems have and Lean doesn't — a standalone, human-readable FIPS 180-4
specification written as mathematics (words, rotations, schedule and compression as
functions over `BitVec 32` / vectors, padding as a proved-correct construction), a
separately written efficient implementation (streaming, and/or a `ByteArray` fold over
blocks), and a kernel-checked equivalence theorem between them closing under only the
standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — which would, as a
by-product, discharge exactly the three `*_eq_spec` axioms SizzLean currently has to
assume for its native hasher, and would give Lean the reusable spec that downstream
work (HMAC, HKDF, SHA-224, Bitcoin/Ethereum components) can state theorems against
instead of against one project's implementation. Before starting, two due-diligence
items: (1) inspect sha2-fv's actual repository and theorem statements — if its Lean
proofs already constitute a spec-level equivalence for SHA-256, the remaining gap
narrows to the standalone/native-bridge pieces; (2) re-read LeanSha256's
`LeanSha256.Core` module docstring in the repo itself, since the ethresear.ch claim of
"proved against the FIPS 180-4 specification" is stronger than its README's own
description, and the exact list of conformance lemmas decides how much of the
spec-equivalence work is genuinely left.

---

## ERRATUM (2026-10-26, Google-first live verification)

This pass's conclusion (the two-level spec + equivalence artifact is open in Lean) is WRONG. Live Google + GitHub search on 2026-10-26 found **remix7531/fips-180-4-lean**: a literate Lean 4 FIPS 180-4 development with separate spec/, impl/ and equiv/ trees and proved sha256_correct / compress_correct theorems (standard axioms, per its AxiomCheck). SHA-256 two-level is **TAKEN** in Lean. Ticket #17 was closed on this evidence before any lane started.
