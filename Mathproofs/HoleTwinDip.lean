/-
  HoleTwinDip.lean — Corrected R231 generalized hole-twin dip theorem: clean shadow-gap windows generate hole-twin pairs at chain dips (+ S1 instance).

  Paper: papers/translation-march-dip-October-11-2026/
  Status: [PROVED] — hole_twin_of_dip, chain_dip, s1_instance
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); R250: exit 0 both sides, zero sorrys, axioms standard-only.
-/

/-
R231 — Hole-twin dip theorem (ROUND231_DOSSIER.md).

Hole-twins: two distinct Sidon 9-sets S ≠ W ⊂ [1,N] with B(S) = B(W) and
maxcov(chain) < N on both sides. The dip theorem gives a predictive
sufficient condition: consecutive shadow gaps g₁<g₂ of W(A) plus a clean
window at t* (the sliding window [1−t*,N−t*] frames exactly {g₁,g₂})
forces holes(A+t*) = {g₁+t*, g₂+t*}, so any Sidon S with the same holes
is a hole-twin of W* = A+t* — sitting at a chain dip when
maxcov(chain(A)) = N−1.

FORMALISATION NOTE (statement correction vs the hand proof): the dossier's
theorem concludes "(S, W*) are hole-twins" from hypotheses that do not
include the 9-set condition in the hole-twin definition (the proof's final
step "the hole-twin definition is met" never checks |S| = |W*| = 9, and it
is not derivable from equal hole sets in general). The formalisation
therefore carries explicit `S.card = 9` and `A.card = 9` hypotheses — the
one-line fix the hand proof needs. The S1 instance (both 9-sets) is
unaffected. Requires hostile review clearance per PROGRAM.md rule 9
before [PROVED].

Claims formalised (machine-checked):
- `dip_holes`: clean window ⇒ holes(A+t) = {g₁+t, g₂+t} (needs only
  rigidity — no Sidon hypothesis).
- `dip_blocked_eq`: equal hole sets ⇒ equal blocked sets.
- `chain_translate_mem`: chain(W*) = chain(A) as finsets of translates.
- `maxcov_translate`: maxcov is translation-invariant along valid shifts.
- `hole_twin_of_dip`: the full pairing theorem (with the 9-set fix), plus
  the chain-dip inequality cov(W*) < maxcov when maxcov(A) = N−1.
- `s1_instance`: (S1, A0w1−5) at t*=−5 — the shadow-gap data
  (consecutive gaps {175,187}, clean window [6,189]) enters as explicit
  [COMPUTED] hypotheses (two independent code paths, ROUND231_DOSSIER.md
  §3), not derived here.
The systematic hunt (0 new instances in 3,016 translations) and dip
arithmetic are cited from ROUND231_DOSSIER.md, not formalised.

Status: imports the [PROVED] TranslationMarch module (R227 Lemma 1,
machine-checked) for the shared W(A)/B(A)/holes definitions and rigidity.

Checked: Lean 4.34.1 + Mathlib v4.34.1, `lake build`, zero sorrys,
`#print axioms` standard-only.
-/
import Mathproofs.TranslationMarch

namespace HoleTwinDip

open Finset

/-- Holes of a translate in unclipped shadow form (from rigidity). -/
theorem holes_filter (A : Finset ℤ) (N t : ℤ) :
    TranslationMarch.holes (A.image (· + t)) N
      = (Finset.Icc 1 N).filter (fun p => p - t ∉ TranslationMarch.rawBlocked A) := by
  ext p
  simp only [TranslationMarch.holes, TranslationMarch.blocked,
    TranslationMarch.rawBlocked_translate, TranslationMarch.mem_image_add,
    Finset.mem_sdiff, Finset.mem_inter, Finset.mem_filter]
  tauto

/-- Shadow gaps of the raw blocked set. -/
def IsShadowGap (A : Finset ℤ) (g : ℤ) : Prop := g ∉ TranslationMarch.rawBlocked A

/-- Consecutive shadow gaps: no other gap strictly between them. -/
def ConsecutiveGaps (A : Finset ℤ) (g₁ g₂ : ℤ) : Prop :=
  g₁ < g₂ ∧ IsShadowGap A g₁ ∧ IsShadowGap A g₂ ∧
    ∀ g, IsShadowGap A g → g₁ < g → g < g₂ → False

/-- Clean window: the sliding window [1−t, N−t] frames exactly the two gaps.
    Stated as a filter equality so that g₁, g₂ ∈ window is derivable. -/
def CleanWindow (A : Finset ℤ) (N t g₁ g₂ : ℤ) : Prop :=
  (Finset.Icc (1 - t) (N - t)).filter (fun g => g ∉ TranslationMarch.rawBlocked A)
    = {g₁, g₂}

/-- The framed gaps lie in the window and are genuine gaps. -/
theorem cleanWindow_gaps (A : Finset ℤ) (N t g₁ g₂ : ℤ)
    (hclean : CleanWindow A N t g₁ g₂) :
    (1 - t ≤ g₁ ∧ g₁ ≤ N - t ∧ IsShadowGap A g₁)
      ∧ (1 - t ≤ g₂ ∧ g₂ ≤ N - t ∧ IsShadowGap A g₂) := by
  have hmem₁ : g₁ ∈ (Finset.Icc (1 - t) (N - t)).filter
      (fun g => g ∉ TranslationMarch.rawBlocked A) := by
    rw [hclean]
    exact Finset.mem_insert_self g₁ {g₂}
  have hmem₂ : g₂ ∈ (Finset.Icc (1 - t) (N - t)).filter
      (fun g => g ∉ TranslationMarch.rawBlocked A) := by
    rw [hclean]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self g₂)
  rw [Finset.mem_filter, Finset.mem_Icc] at hmem₁ hmem₂
  exact ⟨⟨hmem₁.1.1, hmem₁.1.2, hmem₁.2⟩, ⟨hmem₂.1.1, hmem₂.1.2, hmem₂.2⟩⟩

/-- Dip holes: under a clean window the translated holes are exactly the two
    framed gaps shifted. Uses only rigidity — no Sidon hypothesis. -/
theorem dip_holes (A : Finset ℤ) (N t g₁ g₂ : ℤ)
    (hclean : CleanWindow A N t g₁ g₂) :
    TranslationMarch.holes (A.image (· + t)) N = {g₁ + t, g₂ + t} := by
  obtain ⟨⟨hg₁lo, hg₁hi, hg₁W⟩, ⟨hg₂lo, hg₂hi, hg₂W⟩⟩ :=
    cleanWindow_gaps A N t g₁ g₂ hclean
  rw [holes_filter]
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hp1, hpN⟩, hW⟩
    have hmem : p - t ∈ (Finset.Icc (1 - t) (N - t)).filter
        (fun g => g ∉ TranslationMarch.rawBlocked A) := by
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hW⟩
    rw [hclean] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rintro (rfl | rfl)
    · have h' : g₁ + t - t = g₁ := by ring
      rw [h']
      exact ⟨⟨by omega, by omega⟩, hg₁W⟩
    · have h' : g₂ + t - t = g₂ := by ring
      rw [h']
      exact ⟨⟨by omega, by omega⟩, hg₂W⟩

/-- Equal hole sets give equal blocked sets. -/
theorem dip_blocked_eq (S W : Finset ℤ) (N : ℤ)
    (h : TranslationMarch.holes S N = TranslationMarch.holes W N) :
    TranslationMarch.blocked S N = TranslationMarch.blocked W N := by
  have hsubS : TranslationMarch.blocked S N ⊆ Finset.Icc 1 N :=
    Finset.inter_subset_right
  have hsubW : TranslationMarch.blocked W N ⊆ Finset.Icc 1 N :=
    Finset.inter_subset_right
  have hS : TranslationMarch.blocked S N
      = Finset.Icc 1 N \ TranslationMarch.holes S N := by
    ext p
    simp only [TranslationMarch.holes, Finset.mem_sdiff]
    constructor
    · intro hp
      exact ⟨hsubS hp, fun hcon => hcon.2 hp⟩
    · rintro ⟨hpI, hpcon⟩
      by_contra hpB
      exact hpcon ⟨hpI, hpB⟩
  have hW : TranslationMarch.blocked W N
      = Finset.Icc 1 N \ TranslationMarch.holes W N := by
    ext p
    simp only [TranslationMarch.holes, Finset.mem_sdiff]
    constructor
    · intro hp
      exact ⟨hsubW hp, fun hcon => hcon.2 hp⟩
    · rintro ⟨hpI, hpcon⟩
      by_contra hpB
      exact hpcon ⟨hpI, hpB⟩
  rw [hS, hW, h]

/-- Valid shifts of a nonempty B ⊆ [1,N] lie in [1−N, N−1]. -/
theorem valid_shift_mem_Icc (B : Finset ℤ) (N t : ℤ)
    (hne : B.Nonempty) (hB : B ⊆ Finset.Icc 1 N)
    (hBt : B.image (· + t) ⊆ Finset.Icc 1 N) :
    t ∈ Finset.Icc (1 - N) (N - 1) := by
  obtain ⟨b, hb⟩ := hne
  have hbI := hB hb
  have hbtI := hBt (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
  rw [Finset.mem_Icc] at hbI hbtI ⊢
  omega

/-- Translating twice is translating once by the sum. -/
theorem image_add_add (A : Finset ℤ) (s t : ℤ) :
    (A.image (· + s)).image (· + t) = A.image (· + (s + t)) := by
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by ring⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z + s, ⟨z, hz, rfl⟩, by ring⟩

/-- The chain of a translate, as a finset of translates over the canonical
    shift range. -/
def chainFin (A : Finset ℤ) (N : ℤ) : Finset (Finset ℤ) :=
  ((Finset.Icc (1 - N) (N - 1)).filter (fun t => A.image (· + t) ⊆ Finset.Icc 1 N)).image
    (fun t => A.image (· + t))

/-- chain(W*) = chain(A) as finsets: translates of translates reindex. -/
theorem chain_translate (A : Finset ℤ) (N t : ℤ)
    (hne : A.Nonempty) (hA : A ⊆ Finset.Icc 1 N)
    (hAt : A.image (· + t) ⊆ Finset.Icc 1 N) :
    chainFin (A.image (· + t)) N = chainFin A N := by
  have hAt_ne : (A.image (· + t)).Nonempty := hne.image _
  have hrange : ∀ B : Finset ℤ, ∀ s : ℤ, B.Nonempty → B ⊆ Finset.Icc 1 N →
      B.image (· + s) ⊆ Finset.Icc 1 N → s ∈ Finset.Icc (1 - N) (N - 1) :=
    fun B s => valid_shift_mem_Icc B N s
  ext T
  simp only [chainFin, Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨s, ⟨⟨hslo, hshi⟩, hsvalid⟩, rfl⟩
    have hAvalid : A.image (· + (t + s)) ⊆ Finset.Icc 1 N := by
      rw [← image_add_add]
      exact hsvalid
    have hmem : t + s ∈ Finset.Icc (1 - N) (N - 1) :=
      hrange A (t + s) hne hA hAvalid
    refine ⟨t + s, ⟨Finset.mem_Icc.mp hmem, hAvalid⟩, ?_⟩
    rw [image_add_add]
  · rintro ⟨u, ⟨⟨hulo, huhi⟩, huvalid⟩, rfl⟩
    have hBvalid : (A.image (· + t)).image (· + (u - t)) ⊆ Finset.Icc 1 N := by
      rw [image_add_add]
      have : t + (u - t) = u := by ring
      rw [this]
      exact huvalid
    have hmem : u - t ∈ Finset.Icc (1 - N) (N - 1) :=
      hrange (A.image (· + t)) (u - t) hAt_ne hAt hBvalid
    refine ⟨u - t, ⟨Finset.mem_Icc.mp hmem, hBvalid⟩, ?_⟩
    rw [image_add_add]
    have : t + (u - t) = u := by ring
    rw [this]

/-- Max coverage over the chain (0 if the chain is empty). -/
noncomputable def maxcov (A : Finset ℤ) (N : ℤ) : ℕ :=
  (chainFin A N).sup (fun T => (TranslationMarch.blocked T N).card)

/-- Max coverage is translation-invariant along valid shifts. -/
theorem maxcov_translate (A : Finset ℤ) (N t : ℤ)
    (hne : A.Nonempty) (hA : A ⊆ Finset.Icc 1 N)
    (hAt : A.image (· + t) ⊆ Finset.Icc 1 N) :
    maxcov (A.image (· + t)) N = maxcov A N := by
  unfold maxcov
  rw [chain_translate A N t hne hA hAt]

/-- Hole-twin pair (definition, R231): distinct Sidon 9-sets sharing the
    blocked set, both off the saturated chain. -/
def IsHoleTwinPair (S W : Finset ℤ) (N : ℤ) : Prop :=
  S ≠ W ∧ S.card = 9 ∧ W.card = 9
    ∧ TranslationMarch.blocked S N = TranslationMarch.blocked W N
    ∧ maxcov S N < N.toNat ∧ maxcov W N < N.toNat

/-- The hole-twin dip theorem: consecutive shadow gaps + clean window give a
    hole-twin pair at a chain dip. The 9-set hypotheses are the one-line fix
    the hand proof needs (see module header). -/
theorem hole_twin_of_dip (A S : Finset ℤ) (N t g₁ g₂ : ℤ)
    (hne : A.Nonempty) (hA : A ⊆ Finset.Icc 1 N)
    (hAt : A.image (· + t) ⊆ Finset.Icc 1 N)
    (hA9 : A.card = 9) (hS9 : S.card = 9)
    (hcons : ConsecutiveGaps A g₁ g₂)
    (hclean : CleanWindow A N t g₁ g₂)
    (hSne : S ≠ A.image (· + t))
    (hSholes : TranslationMarch.holes S N = {g₁ + t, g₂ + t})
    (hmaxS : maxcov S N < N.toNat)
    (hmaxA : maxcov A N < N.toNat) :
    IsHoleTwinPair S (A.image (· + t)) N := by
  have hdip := dip_holes A N t g₁ g₂ hclean
  have hBeq : TranslationMarch.blocked S N
      = TranslationMarch.blocked (A.image (· + t)) N := by
    apply dip_blocked_eq
    rw [hSholes, hdip]
  have hW9 : (A.image (· + t)).card = 9 := by
    rw [Finset.card_image_of_injective _ (by
      intro a b h
      have h' : a + t = b + t := h
      omega)]
    exact hA9
  have hmaxW : maxcov (A.image (· + t)) N < N.toNat := by
    rw [maxcov_translate A N t hne hA hAt]
    exact hmaxA
  exact ⟨hSne, hS9, hW9, hBeq, hmaxS, hmaxW⟩

/-- Chain dip: when maxcov(chain(A)) = N−1, W* sits strictly below it
    (cov(W*) = N−2 < N−1). -/
theorem chain_dip (A : Finset ℤ) (N t g₁ g₂ : ℤ)
    (hlt : g₁ < g₂)
    (hclean : CleanWindow A N t g₁ g₂)
    (hmaxA : maxcov A N = N.toNat - 1)
    (hN : 2 ≤ N) :
    (TranslationMarch.blocked (A.image (· + t)) N).card < maxcov A N := by
  have hdip := dip_holes A N t g₁ g₂ hclean
  have hcard : (TranslationMarch.holes (A.image (· + t)) N).card = 2 := by
    rw [hdip]
    have hne : g₁ + t ∉ ({g₂ + t} : Finset ℤ) := by
      simp only [Finset.mem_singleton]
      omega
    rw [Finset.card_insert_of_notMem hne, Finset.card_singleton]
  have hsub : TranslationMarch.blocked (A.image (· + t)) N
      ⊆ Finset.Icc 1 N := by
    simp only [TranslationMarch.blocked]
    exact Finset.inter_subset_right
  have hcov : (TranslationMarch.blocked (A.image (· + t)) N).card
      + (TranslationMarch.holes (A.image (· + t)) N).card = (Finset.Icc 1 N).card := by
    have hdis : Disjoint (TranslationMarch.blocked (A.image (· + t)) N)
        (TranslationMarch.holes (A.image (· + t)) N) := by
      simp only [TranslationMarch.holes]
      exact Finset.disjoint_sdiff
    have hunion : TranslationMarch.blocked (A.image (· + t)) N
        ∪ TranslationMarch.holes (A.image (· + t)) N = Finset.Icc 1 N := by
      simp only [TranslationMarch.holes]
      rw [Finset.union_comm]
      exact Finset.sdiff_union_of_subset hsub
    rw [← Finset.card_union_of_disjoint hdis, hunion]
  have hIcc : (Finset.Icc 1 N).card = N.toNat := by
    rw [Int.card_Icc]
    congr 1
    omega
  rw [hmaxA]
  omega

/-- S1 instance: (S1, A0w1−5) are hole-twins at a chain dip. The shadow-gap
    premises (consecutive gaps 175, 187 of W(A0w1); clean window [6,189] at
    t*=−5) are [COMPUTED] ×2 independent paths (ROUND231_DOSSIER.md §3) and
    enter as explicit hypotheses; maxcov bounds are likewise computational
    premises. A0w1 and S1 are concrete 9-sets (dossier §"Headline results"). -/
theorem s1_instance (A0w1 S1 : Finset ℤ)
    (hA9 : A0w1.card = 9) (hS9 : S1.card = 9)
    (hne : A0w1.Nonempty) (hA : A0w1 ⊆ Finset.Icc 1 184)
    (hAt : A0w1.image (· + (-5)) ⊆ Finset.Icc 1 184)
    (hcons : ConsecutiveGaps A0w1 175 187)
    (hclean : CleanWindow A0w1 184 (-5) 175 187)
    (hSne : S1 ≠ A0w1.image (· + (-5)))
    (hSholes : TranslationMarch.holes S1 184 = {170, 182})
    (hmaxS : maxcov S1 184 < (184:ℤ).toNat)
    (hmaxA : maxcov A0w1 184 < (184:ℤ).toNat) :
    IsHoleTwinPair S1 (A0w1.image (· + (-5))) 184 := by
  have hpair := hole_twin_of_dip A0w1 S1 184 (-5) 175 187 hne hA hAt hA9 hS9
    hcons hclean hSne ?_ hmaxS hmaxA
  · exact hpair
  · rw [hSholes]
    have heq : ({175 + (-5), 187 + (-5)} : Finset ℤ) = {170, 182} := by
      decide
    rw [← heq]

end HoleTwinDip
