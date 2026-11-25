/-
  FiberOverlap.lean — R277 fiber-overlap lemmas: autocorrelation bound, overlap identity, top-interval sparsity (Q-23 SURVIVES).

  Paper: papers/sigma-transfer-fiber-overlap-October-11-2026/
  Status: [PROVED] — fiber_overlap, fiber_overlap_identity, autocorr_le_one, top_interval_sparsity
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); R310: bakkie full-library build exit 0, zero sorrys, axioms standard-only.
-/

/-
  FiberOverlap.lean — Lean formalization of Round 277's three lemmas
  (R277 → Mathproofs/FiberOverlap.lean, coordinator lane R290).

  Source: ~/workspace/math-unsolved/ROUND277_DOSSIER.md (Round 277, 2026-10-10).
  Rule-9 hostile review: Q-23 — quoted verdict "SURVIVES" (2026-10-10 21:25 PDT);
  the rule-9 gate is OPEN for these three fiber lemmas.

  Contents:
  (1) Fiber Overlap Lemma (§2 of dossier, [PROVED*]): distinct D-fibers
      s−A, s′−A (s≠s′) intersect in at most 1 point, via the Sidon
      autocorrelation bound |A ∩ (A+t)| ≤ 1 (t≠0).
  (2) F ⟺ F1∧F2 reduction (§1, [PROVED*]): pure logic, no inequalities
      beyond 1+1=2 (R59/R63-clean per dossier).
  (3) Top-interval sparsity (§3, [PROVED*] conditional on T1/T2 [PROVED*]):
      for σ ≤ 91, |D ∩ [σ+1,183]| ≤ σ. The hypotheses hT2/hT1 cite R273's
      T2 [PROVED*] and T1 [PROVED*] with labels intact — the lemma is
      conditional, never a claim about T1/T2 themselves, and T1/T2 are
      never used as established fact.

  Not formalized (staying [COMPUTED] / application-level, by design):
  the 5,813,280-pair scripted audit (r277_audit.py) and the ⌈u/9⌉
  fiber-budget tightening application of the overlap lemma — noted here,
  never stated as theorems.

  Lean 4.34.1 / Mathlib (pin d13f23b723b8a846827a245b89c10fc7d3f11612).
  Zero sorrys. Standard axioms only (propext, Classical.choice, Quot.sound).
-/

import Mathlib

namespace FiberOverlap

/-- Sidon (B₂) property for a finite integer set: pair sums determine the
    summand pair as a multiset. (Dossier §2: the 9-shapes A are Sidon.) -/
def IsSidon (A : Finset ℤ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → ({a, b} : Multiset ℤ) = {c, d}

/-- Dossier §2, autocorrelation bound: |A ∩ (A+t)| ≤ 1 for t ≠ 0.
    Proof: if a≠b both lie in A∩(A+t), write a = a'+t, b = b'+t with
    a',b' ∈ A; then a,b,a',b' ∈ A and a+b' = b+a'. Sidon pair-sum
    uniqueness forces {a,b'} = {b,a'} as multisets; a ≠ b then forces
    a = a', hence t = 0 — contradiction. -/
theorem autocorr_le_one (A : Finset ℤ) (hA : IsSidon A) (t : ℤ) (ht : t ≠ 0) :
    ((A.image (· + t)) ∩ A).card ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨a, ha, b, hb, hne⟩ := Finset.one_lt_card.mp hlt
  rw [Finset.mem_inter] at ha hb
  obtain ⟨ha_img, haA⟩ := ha
  obtain ⟨hb_img, hbA⟩ := hb
  obtain ⟨a', ha'A, ha_eq⟩ := Finset.mem_image.mp ha_img
  obtain ⟨b', hb'A, hb_eq⟩ := Finset.mem_image.mp hb_img
  -- (R294 fix: the old `simp only at ha_eq hb_eq` made no progress — the
  --  mem_image equations are already in applied form.)
  have hsum : a + b' = b + a' := by omega
  have hsidon := hA a haA b' hb'A b hbA a' ha'A hsum
  have hmem : a = b ∨ a = a' := by
    have h1 : a ∈ ({a, b'} : Multiset ℤ) := Multiset.mem_cons_self a {b'}
    rw [hsidon] at h1
    -- `insert` is `cons` for Multiset (defeq); expose the cons form so the
    -- mem_cons/mem_singleton rewrites match syntactically.
    have h1' : a ∈ b ::ₘ ({a'} : Multiset ℤ) := h1
    rw [Multiset.mem_cons, Multiset.mem_singleton] at h1'
    exact h1'
  rcases hmem with h | h
  · exact absurd h hne
  · exfalso
    exact ht (by omega)

/-- D-fiber at pair-sum s: f_s = s − A (dossier §2 notation). -/
def fiber (A : Finset ℤ) (s : ℤ) : Finset ℤ :=
  A.image (fun a => s - a)

/-- Dossier §2, overlap identity: (s−A) ∩ (s′−A) is the image of
    A ∩ (A + (s−s′)) under a ↦ s−a, hence has the same cardinality.
    Proof: x = s−a = s′−a' with a,a' ∈ A gives a = a' + (s−s'),
    i.e. a ∈ A ∩ (A+(s−s′)); conversely a ∈ A ∩ (A+(s−s′)) gives
    s−a ∈ (s−A) ∩ (s′−A) since s−a = s′−(a−(s−s′)). -/
theorem fiber_overlap_identity (A : Finset ℤ) (s s' : ℤ) :
    ((fiber A s) ∩ (fiber A s')).card
      = (A ∩ (A.image (· + (s - s')))).card := by
  have hinj : Function.Injective (fun a : ℤ => s - a) := by
    intro a b hab
    simp only at hab
    omega
  have himg : (fiber A s) ∩ (fiber A s')
      = (A ∩ (A.image (· + (s - s')))).image (fun a => s - a) := by
    ext x
    simp only [fiber, Finset.mem_inter, Finset.mem_image]
    constructor
    · rintro ⟨⟨a, haA, ha⟩, ⟨a', ha'A, ha'⟩⟩
      have h1 : s - a = x := ha
      have h2 : s' - a' = x := ha'
      refine ⟨a, ⟨haA, a', ha'A, ?_⟩, h1⟩
      · show a' + (s - s') = a
        omega
    · rintro ⟨a, ⟨haA, a', ha'A, ha'⟩, ha⟩
      have h1 : a' + (s - s') = a := ha'
      have h2 : s - a = x := ha
      exact ⟨⟨a, haA, h2⟩, ⟨a', ha'A, by show s' - a' = x; omega⟩⟩
  rw [himg]
  exact Finset.card_image_of_injective _ hinj

/-- Dossier §2, Fiber Overlap Lemma [PROVED*]: distinct D-fibers s−A,
    s′−A (s≠s′) intersect in at most 1 point. By the overlap identity
    this is the autocorrelation bound at t = s−s′ ≠ 0. -/
theorem fiber_overlap (A : Finset ℤ) (hA : IsSidon A) (s s' : ℤ)
    (hne : s ≠ s') :
    ((fiber A s) ∩ (fiber A s')).card ≤ 1 := by
  rw [fiber_overlap_identity, Finset.inter_comm]
  exact autocorr_le_one A hA (s - s') (by omega)

/-- Dossier §1, F ⟺ F1∧F2 reduction [PROVED*]: Conjecture F
    (∀ a, e+s ≥ 2) is equivalent to the conjunction of the fragments
    F1 (e=0 ⟹ s≥2) and F2 (s=0 ⟹ e≥2). Forward by specialization;
    backward by case-split: e=0 uses F1, s=0 uses F2, else e≥1∧s≥1.
    Pure logic — the hand proof uses no inequalities beyond 1+1=2. -/
theorem f_iff_f1_f2 {α : Type*} (P : α → ℕ × ℕ) :
    (∀ a, (P a).1 + (P a).2 ≥ 2) ↔
      ((∀ a, (P a).1 = 0 → (P a).2 ≥ 2) ∧
       (∀ a, (P a).2 = 0 → (P a).1 ≥ 2)) := by
  constructor
  · intro h
    exact ⟨fun a ha => by have := h a; rw [ha] at this; omega,
           fun a ha => by have := h a; rw [ha] at this; omega⟩
  · rintro ⟨h1, h2⟩ a
    by_cases he : (P a).1 = 0
    · have hs2 := h1 a he; omega
    · by_cases hs : (P a).2 = 0
      · have he2 := h2 a hs; omega
      · omega

/-- Dossier §3, top-interval sparsity [PROVED*] (conditional):
    for a Sidon 9-shape of span σ ≤ 91, |D ∩ [σ+1,183]| ≤ σ.
    Hypotheses: hT2 is R273's T2 [PROVED*] (reflection gives
    |E_Ā| = u − |D∩[σ+1,183]|, an equality), hT1 is R273's T1 [PROVED*]
    (E-floor |E_Ā| ≥ 183−2σ). Substituting an equality into an
    inequality is pure algebra (direction preserved by construction);
    `omega` closes it over ℕ. Labels cited intact; the lemma is
    conditional on T1/T2 [PROVED*], never a claim about them. -/
theorem top_interval_sparsity (u d σ e : ℕ)
    (hd : d ≤ u) (hu : u = 183 - σ) (hσ : σ ≤ 91)
    (hT2 : u - d = e) (hT1 : e ≥ 183 - 2 * σ) :
    d ≤ σ := by
  omega

#print axioms FiberOverlap.autocorr_le_one
#print axioms FiberOverlap.fiber_overlap_identity
#print axioms FiberOverlap.fiber_overlap
#print axioms FiberOverlap.f_iff_f1_f2
#print axioms FiberOverlap.top_interval_sparsity

end FiberOverlap
