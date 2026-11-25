import Mathlib

/-!
# R155 Branch-SDR endgame (Round 170, Lean formalization lane)

R155 §B (dossier): the SDR endgame. If every maximal H(u,v)-clique `C`
admits distinct V₀-branch representatives — an injection
`φ : C ∖ V₀ → V₀ ∖ B` (the **Branch-SDR**, R155 Lemma, [COMPUTED]
17,050/17,050 on the 55 program pairs) — then
`|C| = b + |C ∖ V₀| ≤ b + (|V₀| − b) = |V₀| = d(v) − 1`,
hence `ω(H(u,v)) ≤ d(v) − 1`.

**Honesty boundary (R159 §A).** The general (R2)-Hall statement
("the residual Z₀-family always has an SDR") was REFUTED as a D*-structural
theorem: two counterexamples on a (d(u), d(v)) = (8, 6) pair violate Hall,
and one even has |C| = 7 > 5 = d(v) − 1, so the bound itself is
*pair-specific*, not graph-specific. This module therefore proves the
**conditional** endgame only: the Branch-SDR (injection `φ`) is an
EXPLICIT HYPOTHESIS, never derived. The pair-specific input — the (6,7)
d(u) < d(v) structure forcing the SDR — is supplied by the caller as
that hypothesis; nothing here smuggles the general (R2)-Hall.

What is formalized:
1. `branch_sdr_endgame`: `φ : ↥(C ∖ V₀) → ↥(V₀ ∖ (C ∩ V₀))` injective
   ⟹ `C.card ≤ V₀.card`. (R155's 3-line §B argument.)
2. `branch_sdr_endgame_clique_bound`: if every H-clique sits inside a
   maximal one and every maximal H-clique carries such a `φ`, then every
   H-clique `K` satisfies `K.card ≤ V₀.card` — i.e. `ω ≤ d(v) − 1` with
   `|V₀| = d(v) − 1`.

This module is standalone (imports only Mathlib). The H-clique framework
definitions (R107/R139/R145) are cited, not re-formalized; the SDR
hypothesis is the clean interface.
-/

/-- R155 §B: Branch-SDR ⟹ |C| ≤ |V₀|. The injection φ (the SDR) is an
explicit hypothesis — its existence is [COMPUTED] on the 55 program pairs
and [OPEN] in general; R159 refuted the general (R2)-Hall, so the
pair-specific form arrives through this hypothesis, never by derivation. -/
theorem branch_sdr_endgame {α : Type*} [DecidableEq α]
    (C V₀ : Finset α)
    (φ : ↥(C \ V₀) → ↥(V₀ \ (C ∩ V₀)))
    (hφ : Function.Injective φ) :
    C.card ≤ V₀.card := by
  -- Partition of C into base points and off-base points.
  have hpart : (C \ V₀).card + (C ∩ V₀).card = C.card :=
    Finset.card_sdiff_add_card_inter C V₀
  -- The SDR is an injection, so off-base points fit in V₀ ∖ (C ∩ V₀).
  have hφcard : (C \ V₀).card ≤ (V₀ \ (C ∩ V₀)).card := by
    have h := Fintype.card_le_of_injective φ hφ
    rwa [Fintype.card_coe, Fintype.card_coe] at h
  -- C ∩ V₀ ⊆ V₀, so |V₀ ∖ (C ∩ V₀)| = |V₀| − |C ∩ V₀|.
  have hsub : C ∩ V₀ ⊆ V₀ := Finset.inter_subset_right
  have hinter : (C ∩ V₀) ∩ V₀ = C ∩ V₀ := by
    ext x
    simp only [Finset.mem_inter]
    tauto
  have hsdiff : (V₀ \ (C ∩ V₀)).card = V₀.card - (C ∩ V₀).card := by
    rw [Finset.card_sdiff, hinter]
  have hle : (C ∩ V₀).card ≤ V₀.card := Finset.card_le_card hsub
  omega

/-- R155 §B consequence: the endgame lifts from maximal cliques to all
H-cliques (every H-clique sits inside a maximal one), giving
ω(H(u,v)) ≤ |V₀| = d(v) − 1. Again the SDR on each maximal clique is an
explicit hypothesis. -/
theorem branch_sdr_endgame_clique_bound {α : Type*} [DecidableEq α]
    (V₀ : Finset α)
    (isHclique isMax : Finset α → Prop)
    (hsub : ∀ K, isHclique K → ∃ C, isMax C ∧ K ⊆ C)
    (hsdr : ∀ C, isMax C →
      ∃ φ : ↥(C \ V₀) → ↥(V₀ \ (C ∩ V₀)), Function.Injective φ)
    (K : Finset α) (hK : isHclique K) :
    K.card ≤ V₀.card := by
  obtain ⟨C, hCmax, hKC⟩ := hsub K hK
  obtain ⟨φ, hφ⟩ := hsdr C hCmax
  exact le_trans (Finset.card_le_card hKC) (branch_sdr_endgame C V₀ φ hφ)

#print axioms branch_sdr_endgame
#print axioms branch_sdr_endgame_clique_bound
