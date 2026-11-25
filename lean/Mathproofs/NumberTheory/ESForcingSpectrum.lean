/-
  ESForcingSpectrum.lean — R313/R316 ES forcing spectrum: S2(a)′ (Q-56), S2(b–d)/S3/S4 (Q-53) — forced/PC/void/split spectrum partition.

  Paper: papers/es-absorption-forcing-October-11-2026/
  Status: [PROVED] — s2a'_forced, s2b_pc, s2c_void, s2d_split, spectrum_partition, psi_union_max
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); R322: 34-theorem batch, bakkie exit 0, zero sorrys, axioms standard-only.
-/

import Mathlib

/-!
# ESForcingSpectrum: the ES forcing spectrum (R313/R316)

Paper trail:
- `~/workspace/math-unsolved/ROUND313_DOSSIER.md` — the new definition: per-cell
  6-class forcing profile σ(c) ∈ {H,C,Fh,Fo,Vh,Vo} of a two-sided-forcing ES
  instance; first theorems S1 (sum identity), S2 (forced-cell characterization),
  S3 (dichotomy), S4 (union monotonicity); C1–C4 corollaries. Rule-9 gate: Q-53
  (Angel, OBJECTION scoped to S2(a) as stated; S1/S2(b–d)/S3/S4/C1–C4 SURVIVE).
- `~/workspace/math-unsolved/ROUND316_DOSSIER.md` — S2(a) repaired as S2(a)′ (the
  dropped `c ∈ u(S)` conjunct restored). Rule-9 gate: Q-56 (Angel, **SURVIVES**,
  2026-10-11 15:57 PDT). Reviewer nits applied (dossier wording: q53 re-run
  "matches the reported numbers"; S4 stated as ψ = max, not a "priority rule";
  literal-failure census unit unweighted; covered sets reconstructed, scoped).
- Stacked on the Q-25/Q-29-gated ESForcingDecomp base (naming cleared by Q-56;
  the base fold itself is still owed — this module is self-contained and does
  not import it).

Formalized here ([PROVED*]-grade, Lean-checked):
- `pcov_subset_u`, `mem_pcov_iff`
- `s2a'_forced` (S2(a)′, Q-56), `s2b_pc`, `s2c_void`, `s2d_split` (S2(b–d), Q-53)
- `spectrum_partition` (S3)
- `psi_union_max` (S4)

C1–C4 corollaries, S1 count identities and the S5 census stay [COMPUTED]×2 —
cited, not formalized (no half-formalization).

R59/R63 audit: S2(a)′ is pure definitional unfolding + quantifier equivalence;
S2(b–d)/S3/S4 use only disjoint unions and case splits — zero monotone-substitution
inequality steps.

Lean 4.34.1 / Mathlib. Zero sorrys. Axioms: standard only (see ROUND322 dossier).
-/

open Finset

namespace ESForcingSpectrum

variable {Cell Fam : Type*} [DecidableEq Cell] [DecidableEq Fam] [Fintype Cell]

variable (covered : Fam → Finset Cell) (p : Fam → Bool)

/-- u(S): union of covered cells. -/
def u (S : Finset Fam) : Finset Cell := S.biUnion covered

/-- Pcov(S): union of prime-covered cells. -/
def pcov (S : Finset Fam) : Finset Cell :=
  S.biUnion fun f => if p f then covered f else ∅

/-- Pcov ⊆ u. -/
theorem pcov_subset_u (S : Finset Fam) : pcov covered p S ⊆ u covered S := by
  intro c hc
  simp only [pcov, Finset.mem_biUnion] at hc
  obtain ⟨f, hf, hfc⟩ := hc
  simp only [u, Finset.mem_biUnion]
  by_cases hpf : p f = true
  · exact ⟨f, hf, by simpa [hpf] using hfc⟩
  · exfalso
    have hempty : c ∈ (∅ : Finset Cell) := by simpa [hpf] using hfc
    simp at hempty

/-- Membership in Pcov, unfolded. -/
theorem mem_pcov_iff (S : Finset Fam) (c : Cell) :
    c ∈ pcov covered p S ↔ ∃ f ∈ S, p f = true ∧ c ∈ covered f := by
  simp only [pcov, Finset.mem_biUnion]
  constructor
  · rintro ⟨f, hf, hfc⟩
    by_cases hpf : p f = true
    · exact ⟨f, hf, hpf, by simpa [hpf] using hfc⟩
    · exfalso
      have hempty : c ∈ (∅ : Finset Cell) := by simpa [hpf] using hfc
      simp at hempty
  · rintro ⟨f, hf, hpf, hfc⟩
    exact ⟨f, hf, by simpa [hpf] using hfc⟩

/-- The six spectrum classes (R313 §1). -/
inductive SpecClass : Type where
  | H : SpecClass   -- hard-forced: c ∈ Pcov ∩ H6
  | C : SpecClass   -- contingent: c ∈ Pcov ∖ H6
  | Fh : SpecClass  -- slack-forced, hard: c ∈ (u ∖ Pcov) ∩ H6
  | Fo : SpecClass  -- slack-forced, open: c ∈ (u ∖ Pcov) ∖ H6
  | Vh : SpecClass  -- void, hard: c ∉ u, c ∈ H6
  | Vo : SpecClass  -- void, open: c ∉ u, c ∉ H6
  deriving DecidableEq

variable (H6 : Finset Cell)

/-- σ_S(c): the per-cell forcing signature (R313 §1). -/
def sigma (S : Finset Fam) (c : Cell) : SpecClass :=
  if c ∈ pcov covered p S then (if c ∈ H6 then .H else .C)
  else if c ∈ u covered S then (if c ∈ H6 then .Fh else .Fo)
  else (if c ∈ H6 then .Vh else .Vo)

/-- S2(a)′: the repaired forced-cell characterization (R316 §2, Q-56 SURVIVES).
    Proof is pure definitional unfolding — the dropped `c ∈ u(S)` conjunct restored. -/
theorem s2a'_forced (S : Finset Fam) (c : Cell) :
    sigma covered p H6 S c = .Fh ∨ sigma covered p H6 S c = .Fo ↔
    c ∈ u covered S ∧ ∀ f ∈ S, c ∈ covered f → p f = false := by
  have hpc : c ∈ pcov covered p S ↔ ∃ f ∈ S, p f = true ∧ c ∈ covered f :=
    mem_pcov_iff covered p S c
  constructor
  · intro h
    by_cases hmem : c ∈ pcov covered p S
    · have hsig : sigma covered p H6 S c = .H ∨ sigma covered p H6 S c = .C := by
        unfold sigma
        rw [if_pos hmem]
        by_cases hh : c ∈ H6 <;> simp [hh]
      rcases h with h | h <;> rcases hsig with h' | h' <;> simp_all
    · have hu : c ∈ u covered S := by
        by_contra hcon
        have hsig : sigma covered p H6 S c = .Vh ∨ sigma covered p H6 S c = .Vo := by
          unfold sigma
          rw [if_neg hmem, if_neg hcon]
          by_cases hh : c ∈ H6 <;> simp [hh]
        rcases h with h | h <;> rcases hsig with h' | h' <;> simp_all
      refine ⟨hu, fun f hf hcf => ?_⟩
      by_contra hpf
      push_neg at hpf
      have hpft : p f = true := by
        cases h : p f with
        | false => exact absurd h hpf
        | true => rfl
      exact hmem (hpc.mpr ⟨f, hf, hpft, hcf⟩)
  · rintro ⟨hu, hall⟩
    have hmem : c ∉ pcov covered p S := by
      intro hmem
      obtain ⟨f, hf, hpft, hcf⟩ := hpc.mp hmem
      have hfalse := hall f hf hcf
      rw [hpft] at hfalse
      cases hfalse
    unfold sigma
    rw [if_neg hmem, if_pos hu]
    by_cases hh : c ∈ H6
    · left; simp [hh]
    · right; simp [hh]

/-- S2(b): pc-secured characterization (Q-53 SURVIVES). -/
theorem s2b_pc (S : Finset Fam) (c : Cell) :
    sigma covered p H6 S c = .H ∨ sigma covered p H6 S c = .C ↔
    c ∈ pcov covered p S := by
  constructor
  · intro h
    by_contra hmem
    have hsig : sigma covered p H6 S c ≠ .H ∧ sigma covered p H6 S c ≠ .C := by
      unfold sigma
      rw [if_neg hmem]
      by_cases hu : c ∈ u covered S <;> by_cases hh : c ∈ H6 <;> simp_all
    rcases h with h | h
    · exact absurd h hsig.1
    · exact absurd h hsig.2
  · intro hmem
    unfold sigma
    rw [if_pos hmem]
    by_cases hh : c ∈ H6
    · left; simp [hh]
    · right; simp [hh]

/-- S2(c): void characterization (Q-53 SURVIVES). -/
theorem s2c_void (S : Finset Fam) (c : Cell) :
    sigma covered p H6 S c = .Vh ∨ sigma covered p H6 S c = .Vo ↔
    c ∉ u covered S := by
  constructor
  · intro h
    by_contra hmem
    by_cases hpc : c ∈ pcov covered p S
    · have hsig : sigma covered p H6 S c = .H ∨ sigma covered p H6 S c = .C := by
        unfold sigma
        rw [if_pos hpc]
        by_cases hh : c ∈ H6 <;> simp [hh]
      rcases h with h | h <;> rcases hsig with h' | h' <;> simp_all
    · have hsig : sigma covered p H6 S c = .Fh ∨ sigma covered p H6 S c = .Fo := by
        unfold sigma
        rw [if_neg hpc, if_pos hmem]
        by_cases hh : c ∈ H6 <;> simp [hh]
      rcases h with h | h <;> rcases hsig with h' | h' <;> simp_all
  · intro hmem
    have hpc : c ∉ pcov covered p S :=
      fun h => hmem (pcov_subset_u covered p S h)
    unfold sigma
    rw [if_neg hpc, if_neg hmem]
    by_cases hh : c ∈ H6
    · left; simp [hh]
    · right; simp [hh]

/-- S2(d): the hard/open split is exactly the c ∈ H6 check (Q-53 SURVIVES). -/
theorem s2d_split (S : Finset Fam) (c : Cell) :
    (sigma covered p H6 S c = .H ∨ sigma covered p H6 S c = .Fh ∨
      sigma covered p H6 S c = .Vh) ↔ c ∈ H6 := by
  unfold sigma
  by_cases hpc : c ∈ pcov covered p S <;> by_cases hu : c ∈ u covered S <;>
    by_cases hh : c ∈ H6 <;> simp_all

/-- S3: the six classes partition the universe (Q-53 SURVIVES). -/
theorem spectrum_partition (S : Finset Fam) (c : Cell) :
    (sigma covered p H6 S c = .H ∨ sigma covered p H6 S c = .C ∨
      sigma covered p H6 S c = .Fh ∨ sigma covered p H6 S c = .Fo ∨
      sigma covered p H6 S c = .Vh ∨ sigma covered p H6 S c = .Vo) ∧
    (sigma covered p H6 S c = .H → sigma covered p H6 S c ≠ .C ∧
      sigma covered p H6 S c ≠ .Fh ∧ sigma covered p H6 S c ≠ .Fo ∧
      sigma covered p H6 S c ≠ .Vh ∧ sigma covered p H6 S c ≠ .Vo) := by
  unfold sigma
  by_cases hpc : c ∈ pcov covered p S <;> by_cases hu : c ∈ u covered S <;>
    by_cases hh : c ∈ H6 <;> simp_all

/-- ψ_S(c): the 0/1/2 priority collapse ({Vh,Vo}/{Fh,Fo}/{H,C}). -/
def psi (S : Finset Fam) (c : Cell) : ℕ :=
  if c ∈ pcov covered p S then 2 else if c ∈ u covered S then 1 else 0

/-- S4: union monotonicity — ψ_{S∪T} = max (Q-53 SURVIVES; Q-56 confirms the
    pc-secured-wins form is just ψ = max restated, not an extra assumption). -/
theorem psi_union_max (S T : Finset Fam) (c : Cell) :
    psi covered p (S ∪ T) c = max (psi covered p S c) (psi covered p T c) := by
  have hu : u covered (S ∪ T) = u covered S ∪ u covered T :=
    Finset.union_biUnion
  have hpc : pcov covered p (S ∪ T) = pcov covered p S ∪ pcov covered p T :=
    Finset.union_biUnion
  have h2 : ∀ (X : Finset Fam), c ∈ pcov covered p X → psi covered p X c = 2 := by
    intro X hX
    unfold psi
    rw [if_pos hX]
  have h1 : ∀ (X : Finset Fam), c ∈ u covered X → c ∉ pcov covered p X →
      psi covered p X c = 1 := by
    intro X hXu hXp
    unfold psi
    rw [if_neg hXp, if_pos hXu]
  have h0 : ∀ (X : Finset Fam), c ∉ u covered X → psi covered p X c = 0 := by
    intro X hXu
    unfold psi
    rw [if_neg (fun h => hXu (pcov_subset_u covered p X h)), if_neg hXu]
  have hle2 : ∀ (X : Finset Fam), psi covered p X c ≤ 2 := by
    intro X
    by_cases hpt : c ∈ pcov covered p X
    · rw [h2 X hpt]
    · by_cases hut : c ∈ u covered X
      · rw [h1 X hut hpt]; decide
      · rw [h0 X hut]; decide
  by_cases hps : c ∈ pcov covered p S
  · rw [h2 S hps, h2 (S ∪ T) (by rw [hpc]; exact Finset.mem_union_left _ hps)]
    exact (Nat.max_eq_left (hle2 T)).symm
  · by_cases hpt : c ∈ pcov covered p T
    · rw [h2 T hpt, h2 (S ∪ T) (by rw [hpc]; exact Finset.mem_union_right _ hpt)]
      exact (Nat.max_eq_right (hle2 S)).symm
    · have hSTn : c ∉ pcov covered p (S ∪ T) := by
        rw [hpc]
        simp [Finset.mem_union, hps, hpt]
      by_cases hus : c ∈ u covered S
      · by_cases hut : c ∈ u covered T
        · rw [h1 S hus hps, h1 T hut hpt,
            h1 (S ∪ T) (by rw [hu]; exact Finset.mem_union_left _ hus) hSTn]
          decide
        · rw [h1 S hus hps, h0 T hut,
            h1 (S ∪ T) (by rw [hu]; exact Finset.mem_union_left _ hus) hSTn]
          decide
      · by_cases hut : c ∈ u covered T
        · rw [h0 S hus, h1 T hut hpt,
            h1 (S ∪ T) (by rw [hu]; exact Finset.mem_union_right _ hut) hSTn]
          decide
        · rw [h0 S hus, h0 T hut,
            h0 (S ∪ T) (by rw [hu]; simp [Finset.mem_union, hus, hut])]
          decide

end ESForcingSpectrum
