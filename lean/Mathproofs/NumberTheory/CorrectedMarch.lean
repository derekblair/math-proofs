/-
  CorrectedMarch.lean — R235 corrected theorems: ψ-translate identities (Theorem 2*) + corrected saturated chain/width bounds (Corollary 1*).

  Paper: papers/translation-march-dip-October-11-2026/
  Status: [PROVED] — psi_as_phi_translate, feas_iff, chain_bounds, chain_width
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); R246: bakkie `lake build` exit 0, zero sorrys, axioms standard-only.
-/

/-
R235 — Corrected Theorem 2* (ψ-translate identities) + Corollary 1*
(saturated chain with containment).

Claims formalised (machine-checked):
- `psi_as_phi_translate`: ψ_c(S) = φ(S) − (185−c) as sets, all S, c
  (scalar identity φ(a)−(185−c) = c−a, lifted to images).
- `psi184_translate`: ψ₁₈₄(Astar) = φ(Astar) − 1 (direct).
- `psi182_E4`: for E4 = Astar−1, ψ₁₈₂(E4) = φ(Astar) − 2
  (distinguishing fact, [COMPUTED]: holes(φ(Astar)−1)=∅,
  holes(φ(Astar)−2)={184} — not formalised here).
- `feas_iff`: for nonempty finite A ⊆ [1,N], m = min A, M = max A:
  A+t ⊆ [1,N] ⟺ 1−m ≤ t ≤ N−M.
- `chain_bounds`: with the granted saturation iff-cores
  (t≥0: sat t ⟺ t ≤ λ; t≤0: sat t ⟺ −η ≤ t) and feasibility,
  feasible ∧ saturated ⟺ max(−η,1−m) ≤ t ≤ min(λ,N−M).
- `chain_zero_mem`: t=0 always qualifies (non-emptiness).
- `chain_width`: width = min(λ,N−M) + min(η,m−1) + 1.

Status: both theorems SURVIVED the PROGRAM.md rule-9 hostile re-review
(R238 Phase 3, Codex gpt-6-astra/ultra on bakkie; transcripts in
review-r235/) — no fresh review needed for this module. The [COMPUTED]
E4 = Astar−1 premise and holes data are cited from ROUND235_DOSSIER.md,
not formalised.

Checked: Lean 4.34.1 + Mathlib v4.34.1, `lake build`, zero sorrys,
`#print axioms` standard-only.
-/
import Mathlib

namespace CorrectedMarch

open Finset

/-- φ(a) = 185 − a (reflection). -/
def phi : ℤ → ℤ := fun a => 185 - a

/-- ψ_c(a) = c − a. -/
def psi (c : ℤ) : ℤ → ℤ := fun a => c - a

/-- The scalar identity, lifted: ψ_c(S) = φ(S) − (185−c) as sets. -/
theorem psi_as_phi_translate (S : Finset ℤ) (c : ℤ) :
    S.image (psi c) = (S.image phi).image (· - (185 - c)) := by
  ext x
  simp only [Finset.mem_image, psi, phi]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨185 - a, ⟨a, ha, rfl⟩, by ring⟩
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, by ring⟩

/-- Theorem 2*, first identity: ψ₁₈₄(Astar) = φ(Astar) − 1. -/
theorem psi184_translate (S : Finset ℤ) :
    S.image (psi 184) = (S.image phi).image (· - 1) := by
  ext x
  simp only [Finset.mem_image, psi, phi]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨185 - a, ⟨a, ha, rfl⟩, by ring⟩
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, by ring⟩

/-- Theorem 2*, second identity: for E4 = Astar−1, ψ₁₈₂(E4) = φ(Astar) − 2.
    (The [COMPUTED] premise E4 = Astar−1 is an input, not proved here.) -/
theorem psi182_E4 (Astar : Finset ℤ) :
    (Astar.image (· - 1)).image (psi 182) = (Astar.image phi).image (· - 2) := by
  rw [Finset.image_image, Finset.image_image]
  congr 1
  funext a
  simp only [Function.comp_apply, psi, phi]
  ring

/-- Feasibility: for nonempty finite A ⊆ [1,N] with m = min A, M = max A,
    A+t ⊆ [1,N] ⟺ 1−m ≤ t ≤ N−M. -/
theorem feas_iff (A : Finset ℤ) (N m M : ℤ) (t : ℤ)
    (hne : A.Nonempty) (hm : m = A.min' hne) (hM : M = A.max' hne) :
    (A.image (· + t) ⊆ Finset.Icc 1 N) ↔ 1 - m ≤ t ∧ t ≤ N - M := by
  have hmA : m ∈ A := hm.symm ▸ A.min'_mem hne
  have hMA : M ∈ A := hM.symm ▸ A.max'_mem hne
  constructor
  · intro h
    have hmem1 : m + t ∈ A.image (· + t) := Finset.mem_image.mpr ⟨m, hmA, rfl⟩
    have hmem2 : M + t ∈ A.image (· + t) := Finset.mem_image.mpr ⟨M, hMA, rfl⟩
    have h1 : m + t ∈ Finset.Icc 1 N := h hmem1
    have h2 : M + t ∈ Finset.Icc 1 N := h hmem2
    rw [Finset.mem_Icc] at h1 h2
    omega
  · rintro ⟨hlo, hhi⟩ a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    have hmin : m ≤ b := by
      rw [hm]; exact A.min'_le b hb
    have hmax : b ≤ M := by
      rw [hM]; exact A.le_max' b hb
    rw [Finset.mem_Icc]
    omega

/-- Corollary 1*: intersecting the granted saturation range with the
    feasibility range. The iff-cores are the granted premises:
    t≥0: sat t ⟺ t ≤ λ (monotone); t≤0: sat t ⟺ −η ≤ t (symmetric). -/
theorem chain_bounds (N m M lam eta t : ℤ)
    (hlam : 0 ≤ lam) (heta : 0 ≤ eta)
    (hm : 1 ≤ m)
    (sat : ℤ → Prop)
    (hPos : ∀ t : ℤ, 1 ≤ t → (sat t ↔ t ≤ lam))
    (hNeg : ∀ t : ℤ, t ≤ 0 → (sat t ↔ -eta ≤ t)) :
    ((1 - m ≤ t ∧ t ≤ N - M) ∧ sat t)
      ↔ (max (-eta) (1 - m) ≤ t ∧ t ≤ min lam (N - M)) := by
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hsat⟩
    rcases le_or_gt 1 t with ht | ht
    · rw [(hPos t ht)] at hsat
      exact ⟨by omega, by omega⟩
    · have ht0 : t ≤ 0 := by omega
      rw [(hNeg t ht0)] at hsat
      exact ⟨by omega, by omega⟩
  · rintro ⟨hlo, hhi⟩
    rcases le_or_gt 1 t with ht | ht
    · exact ⟨⟨by omega, by omega⟩, (hPos t ht).mpr (by omega)⟩
    · have ht0 : t ≤ 0 := by omega
      exact ⟨⟨by omega, by omega⟩, (hNeg t ht0).mpr (by omega)⟩

/-- The chain is nonempty: t=0 always qualifies on both sides. -/
theorem chain_zero_mem (N m M lam eta : ℤ)
    (hlam : 0 ≤ lam) (heta : 0 ≤ eta)
    (hm : 1 ≤ m) (hM : M ≤ N)
    (sat : ℤ → Prop)
    (hNeg : ∀ t : ℤ, t ≤ 0 → (sat t ↔ -eta ≤ t)) :
    (1 - m ≤ 0 ∧ 0 ≤ N - M) ∧ sat 0 := by
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  rw [(hNeg 0 le_rfl)]
  omega

/-- Corollary 1*: width = min(λ,N−M) + min(η,m−1) + 1, from
    −max(−η,1−m) = min(η,m−1). -/
theorem chain_width (N m M lam eta : ℤ)
    (hlam : 0 ≤ lam) (heta : 0 ≤ eta)
    (hm : 1 ≤ m) (hMN : m ≤ M) (hM : M ≤ N) :
    ((Finset.Icc (max (-eta) (1 - m)) (min lam (N - M))).card : ℤ)
      = min lam (N - M) + min eta (m - 1) + 1 := by
  have hle : max (-eta) (1 - m) ≤ min lam (N - M) := by omega
  rw [Int.card_Icc]
  rw [Int.toNat_of_nonneg (by omega :
    (0:ℤ) ≤ min lam (N - M) + 1 - max (-eta) (1 - m))]
  push_cast
  omega
