/-
  TranslationMarch.lean — R227 Translation March (surviving core): Lemma 1, Theorem 1, Corollary 1 iff-core/monotonicity — rigid translation of blocked sets, march, saturation iff shadow.

  Paper: papers/translation-march-dip-October-11-2026/
  Status: [PROVED] — rawBlocked_translate, rigidity, march, march_neg, march_saturated_iff_shadow, plateau_downward
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); R234: bakkie exit 0 (8924/8924) + local exit 0, zero sorrys, axioms standard-only.
-/

/-
R227 — Translation March theorem (ROUND227_DOSSIER.md).

Claims formalised (machine-checked) — all SURVIVED the PROGRAM.md rule-9
hostile review (Codex gpt-6-astra/ultra on bakkie, 2026-10-09; transcript in
~/workspace/math-unsolved/review-r227/, verdict FAILS-as-written):
- Lemma 1 (translation rigidity): B(A+t) = (W(A)+t) ∩ [1,N]
  (`rawBlocked_translate`, `rigidity`). Review: "the injectivity argument is
  correct and sufficient."
- Theorem 1 (translation march): for saturated A and t ≥ 0 with A+t ⊆ [1,N],
  holes(A+t) sit in the bottom t positions and are exactly the shadow gaps
  of W(A) (`march`); the t ≤ 0 half marches from the top (`march_neg`).
  Review: "the interval arithmetic and exact hole descriptions survive."
- Corollary 1 CORE (saturated chain): A+t saturated ⟺ the shadow window
  [1−t,0] ⊆ W(A) (`march_saturated_iff_shadow`); the saturated plateau is
  downward-closed in t (`plateau_downward`). Review: "finiteness and
  monotonicity survive"; the formalisation carries the explicit
  A+t ⊆ [1,N] containment the review demands.
NOT formalised (demoted to [OPEN] per the review gate — see dossier):
- Corollary 1's chain/width framing ("maximal saturated translation
  interval", width λ+η+1) — omits the containment restriction.
- Theorem 2's "both chain translations" assertion — false as stated
  (φ(Astar)−2 has hole {184}); the ψ-identities themselves survive.
The [COMPUTED] instantiations (Astar/C shadow tables, march tables |t|≤6,
sharing-pair equalities) are cited from ROUND227_DOSSIER.md, not formalised.

Checked: Lean 4.34.1 + Mathlib v4.34.1, `lake build`, zero sorrys,
`#print axioms` standard-only.
-/
import Mathlib

namespace TranslationMarch

open Finset

/-- Pair sums P(A) = {a+a' : a,a' ∈ A}. The dossier uses i≤j; the set of
    sums is identical. -/
def pairSums (A : Finset ℤ) : Finset ℤ :=
  (A ×ˢ A).image (fun p : ℤ × ℤ => p.1 + p.2)

theorem mem_pairSums {A : Finset ℤ} {s : ℤ} :
    s ∈ pairSums A ↔ ∃ a ∈ A, ∃ b ∈ A, a + b = s := by
  unfold pairSums
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, hmem, rfl⟩
    rw [Finset.mem_product] at hmem
    obtain ⟨ha, hb⟩ := hmem
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨⟨a, b⟩, Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩

/-- Raw blocked set W(A) (R227's new definition): the unclipped formula. -/
def rawBlocked (A : Finset ℤ) : Finset ℤ :=
  A ∪ (((pairSums A) ×ˢ A).image (fun p : ℤ × ℤ => p.1 - p.2)
    ∪ ((pairSums A).filter (fun s => s % 2 = 0)).image (fun s => s / 2))

/-- Blocked set B(A): raw formula clipped to [1,N]. -/
def blocked (A : Finset ℤ) (N : ℤ) : Finset ℤ :=
  rawBlocked A ∩ Finset.Icc 1 N

/-- Holes: positions in [1,N] not blocked. -/
def holes (A : Finset ℤ) (N : ℤ) : Finset ℤ :=
  Finset.Icc 1 N \ blocked A N

/-- Membership in an image under translation. -/
theorem mem_image_add (A : Finset ℤ) (t x : ℤ) :
    x ∈ A.image (· + t) ↔ x - t ∈ A := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    refine ⟨x - t, h, ?_⟩
    show x - t + t = x
    ring

theorem rawBlocked_empty : rawBlocked ∅ = ∅ := by
  simp [rawBlocked, pairSums]

/-- Explicit membership characterisation of the raw blocked set. -/
theorem mem_rawBlocked {A : Finset ℤ} {w : ℤ} :
    w ∈ rawBlocked A ↔
      w ∈ A ∨ (∃ s ∈ pairSums A, ∃ a ∈ A, s - a = w)
        ∨ (∃ s ∈ pairSums A, s % 2 = 0 ∧ s / 2 = w) := by
  simp only [rawBlocked, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · obtain ⟨x, hmem, rfl⟩ := h
      obtain ⟨s, a⟩ := x
      rw [Finset.mem_product] at hmem
      obtain ⟨hs, ha⟩ := hmem
      exact Or.inr (Or.inl ⟨s, hs, a, ha, rfl⟩)
    · obtain ⟨s, hmem, rfl⟩ := h
      obtain ⟨hs, hev⟩ := hmem
      exact Or.inr (Or.inr ⟨s, hs, hev, rfl⟩)
  · rintro (h | h | h)
    · exact Or.inl h
    · obtain ⟨s, hs, a, ha, rfl⟩ := h
      exact Or.inr (Or.inl ⟨(s, a), Finset.mem_product.mpr ⟨hs, ha⟩, rfl⟩)
    · obtain ⟨s, hs, hev, rfl⟩ := h
      exact Or.inr (Or.inr ⟨s, ⟨hs, hev⟩, rfl⟩)

/-- Pair sums commute with translation: P(A+t) = P(A) + 2t. -/
theorem pairSums_translate (A : Finset ℤ) (t : ℤ) :
    pairSums (A.image (· + t)) = (pairSums A).image (· + 2 * t) := by
  ext s
  rw [mem_pairSums]
  simp only [mem_pairSums, mem_image_add]
  constructor
  · rintro ⟨a, ha, b, hb, hsum⟩
    exact ⟨a - t, ha, b - t, hb, by omega⟩
  · rintro ⟨a, ha, b, hb, hsum⟩
    refine ⟨a + t, by simpa using ha, b + t, by simpa using hb, by omega⟩

/-- The midpoint component shifts by t: (s+2t)/2 = s/2 + t for even s. -/
theorem ediv_shift (s t : ℤ) (h : s % 2 = 0) :
    (s + 2 * t) / 2 = s / 2 + t := by
  omega

/-- Lemma 1 (translation rigidity): the raw blocked set commutes with
    translation. The proof is pure set algebra — no Sidon distinctness used. -/
theorem rawBlocked_translate (A : Finset ℤ) (t : ℤ) :
    rawBlocked (A.image (· + t)) = (rawBlocked A).image (· + t) := by
  ext w
  rw [mem_rawBlocked, mem_image_add (rawBlocked A) t w, mem_rawBlocked]
  constructor
  · rintro (h | h | h)
    · exact Or.inl ((mem_image_add A t w).mp h)
    · obtain ⟨s, hsP, a, haA, rfl⟩ := h
      rw [pairSums_translate] at hsP
      have hsA : s - 2 * t ∈ pairSums A := (mem_image_add _ _ _).mp hsP
      refine Or.inr (Or.inl ⟨s - 2 * t, hsA, a - t,
        (mem_image_add A t a).mp haA, by omega⟩)
    · obtain ⟨s, hsP, hev, rfl⟩ := h
      rw [pairSums_translate] at hsP
      have hsA : s - 2 * t ∈ pairSums A := (mem_image_add _ _ _).mp hsP
      have hev' : (s - 2 * t) % 2 = 0 := by omega
      refine Or.inr (Or.inr ⟨s - 2 * t, hsA, hev', by omega⟩)
  · rintro (h | h | h)
    · exact Or.inl ((mem_image_add A t w).mpr h)
    · obtain ⟨s, hsA, a, haA, hseq⟩ := h
      have hsP : s + 2 * t ∈ pairSums (A.image (· + t)) := by
        rw [pairSums_translate]
        apply (mem_image_add _ _ _).mpr
        simpa using hsA
      have haA' : a + t ∈ A.image (· + t) := by
        apply (mem_image_add _ _ _).mpr
        simpa using haA
      refine Or.inr (Or.inl ⟨s + 2 * t, hsP, a + t, haA', by omega⟩)
    · obtain ⟨s, hsA, hev, hseq⟩ := h
      have hsP : s + 2 * t ∈ pairSums (A.image (· + t)) := by
        rw [pairSums_translate]
        apply (mem_image_add _ _ _).mpr
        simpa using hsA
      have hev' : (s + 2 * t) % 2 = 0 := by omega
      refine Or.inr (Or.inr ⟨s + 2 * t, hsP, hev', by omega⟩)

/-- Lemma 1, clipped form: B(A+t) = (W(A)+t) ∩ [1,N]. -/
theorem rigidity (A : Finset ℤ) (N t : ℤ) :
    blocked (A.image (· + t)) N
      = (rawBlocked A).image (· + t) ∩ Finset.Icc 1 N := by
  unfold blocked
  rw [rawBlocked_translate]

/-- Image of [1,N] under translation. -/
theorem image_Icc_add (N t : ℤ) :
    (Finset.Icc 1 N).image (· + t) = Finset.Icc (1 + t) (N + t) := by
  ext x
  rw [mem_image_add]
  simp only [Finset.mem_Icc]
  omega

/-- A saturated set is nonempty (1 must be blocked by something). -/
theorem nonempty_of_saturated (A : Finset ℤ) (N : ℤ)
    (hN : 1 ≤ N) (hsat : Finset.Icc 1 N ⊆ rawBlocked A) : A.Nonempty := by
  by_contra hcon
  rw [Finset.not_nonempty_iff_eq_empty] at hcon
  have h1 : (1:ℤ) ∈ rawBlocked A := hsat (Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩)
  rw [hcon, rawBlocked_empty] at h1
  exact Finset.notMem_empty 1 h1

/-- Theorem 1 (translation march, t ≥ 0): for saturated A, translating by t
    sweeps holes from the bottom — hole positions are exactly the shadow gaps
    of W(A) in the window [1−t, 0]. -/
theorem march (A : Finset ℤ) (N t : ℤ)
    (hN : 1 ≤ N)
    (hA : A ⊆ Finset.Icc 1 N)
    (hsat : Finset.Icc 1 N ⊆ rawBlocked A)
    (hAt : (A.image (· + t)) ⊆ Finset.Icc 1 N)
    (ht : 0 ≤ t) :
    holes (A.image (· + t)) N
      = (Finset.Icc 1 t).filter (fun p => p - t ∉ rawBlocked A) := by
  obtain ⟨a0, ha0⟩ := nonempty_of_saturated A N hN hsat
  have ha0mem := hA ha0
  rw [Finset.mem_Icc] at ha0mem
  have hatmem := hAt (Finset.mem_image.mpr ⟨a0, ha0, rfl⟩)
  rw [Finset.mem_Icc] at hatmem
  have htN : t ≤ N := by omega
  have hmem : ∀ p : ℤ, p ∈ (rawBlocked A).image (· + t) ↔ p - t ∈ rawBlocked A :=
    fun p => mem_image_add _ _ _
  ext p
  simp only [holes, blocked, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_Icc,
    Finset.mem_filter]
  rw [rawBlocked_translate,
    show p ∈ (rawBlocked A).image (· + t) ↔ p - t ∈ rawBlocked A from hmem p]
  constructor
  · rintro ⟨⟨hp1, hpN⟩, hnb⟩
    have hpt : p ≤ t := by
      by_contra hcon
      have hlt : t < p := lt_of_not_ge hcon
      have hpimg : p - t ∈ rawBlocked A := by
        have hsub : (Finset.Icc 1 N).image (· + t)
            ⊆ (rawBlocked A).image (· + t) :=
          Finset.image_subset_image hsat
        rw [image_Icc_add] at hsub
        have hpmem : p ∈ Finset.Icc (1 + t) (N + t) :=
          Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have hmem' := hsub hpmem
        rwa [hmem p] at hmem'
      exact hnb ⟨hpimg, hp1, hpN⟩
    exact ⟨⟨hp1, hpt⟩, fun h => hnb ⟨h, hp1, hpN⟩⟩
  · rintro ⟨⟨hp1, hpt⟩, hshadow⟩
    refine ⟨⟨hp1, by omega⟩, ?_⟩
    rintro ⟨himg, _, _⟩
    exact hshadow himg

/-- Theorem 1 (translation march, t ≤ 0): holes sweep from the top. -/
theorem march_neg (A : Finset ℤ) (N t : ℤ)
    (hN : 1 ≤ N)
    (hA : A ⊆ Finset.Icc 1 N)
    (hsat : Finset.Icc 1 N ⊆ rawBlocked A)
    (hAt : (A.image (· + t)) ⊆ Finset.Icc 1 N)
    (ht : t ≤ 0) :
    holes (A.image (· + t)) N
      = (Finset.Icc (N + t + 1) N).filter (fun p => p - t ∉ rawBlocked A) := by
  obtain ⟨a0, ha0⟩ := nonempty_of_saturated A N hN hsat
  have ha0mem := hA ha0
  rw [Finset.mem_Icc] at ha0mem
  have hatmem := hAt (Finset.mem_image.mpr ⟨a0, ha0, rfl⟩)
  rw [Finset.mem_Icc] at hatmem
  have hNt : 1 ≤ N + t := by omega
  have hmem : ∀ p : ℤ, p ∈ (rawBlocked A).image (· + t) ↔ p - t ∈ rawBlocked A :=
    fun p => mem_image_add _ _ _
  ext p
  simp only [holes, blocked, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_Icc,
    Finset.mem_filter]
  rw [rawBlocked_translate,
    show p ∈ (rawBlocked A).image (· + t) ↔ p - t ∈ rawBlocked A from hmem p]
  constructor
  · rintro ⟨⟨hp1, hpN⟩, hnb⟩
    have hpt : N + t + 1 ≤ p := by
      by_contra hcon
      have hlt : p < N + t + 1 := lt_of_not_ge hcon
      have hpimg : p - t ∈ rawBlocked A := by
        have hsub : (Finset.Icc 1 N).image (· + t)
            ⊆ (rawBlocked A).image (· + t) :=
          Finset.image_subset_image hsat
        rw [image_Icc_add] at hsub
        have hpmem : p ∈ Finset.Icc (1 + t) (N + t) :=
          Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have hmem' := hsub hpmem
        rwa [hmem p] at hmem'
      exact hnb ⟨hpimg, hp1, hpN⟩
    exact ⟨⟨hpt, hpN⟩, fun h => hnb ⟨h, hp1, hpN⟩⟩
  · rintro ⟨⟨hp1, hpN⟩, hshadow⟩
    refine ⟨⟨by omega, hpN⟩, ?_⟩
    rintro ⟨himg, _, _⟩
    exact hshadow himg

/-- Corollary 1 (saturated chain): A+t stays saturated exactly while the
    shadow window [1−t,0] is covered by W(A). -/
theorem march_saturated_iff_shadow (A : Finset ℤ) (N t : ℤ)
    (hN : 1 ≤ N)
    (hA : A ⊆ Finset.Icc 1 N)
    (hsat : Finset.Icc 1 N ⊆ rawBlocked A)
    (hAt : (A.image (· + t)) ⊆ Finset.Icc 1 N)
    (ht : 0 ≤ t) :
    holes (A.image (· + t)) N = ∅ ↔ Finset.Icc (1 - t) 0 ⊆ rawBlocked A := by
  rw [march A N t hN hA hsat hAt ht, Finset.filter_eq_empty_iff]
  constructor
  · intro h x hx
    have hp : x + t ∈ Finset.Icc 1 t := by
      rw [Finset.mem_Icc] at hx ⊢
      omega
    have hxW := h (x := x + t) hp
    have hxW' : ¬ ((x + t) - t ∉ rawBlocked A) := hxW
    rw [show (x + t) - t = x from by ring] at hxW'
    simpa using hxW'
  · intro h p hp
    have hI : p - t ∈ Finset.Icc (1 - t) 0 := by
      rw [Finset.mem_Icc] at hp ⊢
      omega
    have hw : p - t ∈ rawBlocked A := h hI
    show ¬ ((p - t) ∉ rawBlocked A)
    simpa using hw

/-- The saturated plateau is downward-closed in t: saturation at t implies
    saturation at every smaller s ≥ 0 (the "monotone in t" step of
    Corollary 1's proof). -/
theorem plateau_downward (A : Finset ℤ) (N s t : ℤ)
    (hN : 1 ≤ N)
    (hA : A ⊆ Finset.Icc 1 N)
    (hsat : Finset.Icc 1 N ⊆ rawBlocked A)
    (hAt : (A.image (· + t)) ⊆ Finset.Icc 1 N)
    (hAs : (A.image (· + s)) ⊆ Finset.Icc 1 N)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : 0 ≤ t)
    (hsat_t : holes (A.image (· + t)) N = ∅) :
    holes (A.image (· + s)) N = ∅ := by
  rw [march_saturated_iff_shadow A N t hN hA hsat hAt ht] at hsat_t
  rw [march_saturated_iff_shadow A N s hN hA hsat hAs hs]
  intro x hx
  exact hsat_t (by
    rw [Finset.mem_Icc] at hx ⊢
    omega)

end TranslationMarch
