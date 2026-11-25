/-
  MarchLadderCeiling.lean — R259 Theorem 6 two-sided ladder ceiling + R263 catalog ceiling (L≤10 unattained).

  Paper: papers/subfamily-ladder-ceiling-October-11-2026/
  Status: [PROVED] — theorem6, catalog_ceiling (+ one-sided/binding variants)
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); R310: bakkie full-library build exit 0 (17,936 jobs), zero sorrys; axioms [propext, Quot.sound].
-/

/-
  MarchLadderCeiling.lean — Lean formalization of R259's Theorem 6
  (two-sided ladder-length ceiling for single-gap hole-twin ladders).

  Source: ~/workspace/math-unsolved/ROUND259_DOSSIER.md (Round 259, 2026-10-10).
  Rule-9 hostile review: ~/workspace/math-unsolved/review-r259-theorem6/
  (Codex gpt-6-astra / ultra) — verdict: "The proof survives under the
  Theorem 4 characterization explicitly granted in the file. There is no
  arithmetic, direction, or off-by-one error." (12/12 targeted checks
  correct.) The reviewer notes the substantive dependency: each side
  frames the same fixed shadow gap throughout the ladder (R257's
  characterization), which could not be independently verified against
  the original R257 text — it is cited here as hypotheses
  (`hmeetA`/`hmeetB`), not re-proved.

  Reviewer exposition nits are addressed: the rung interval [t₀,t₁] is
  distinguished from the translation parameter s (each rung s uses the
  window [1−s, 184−s]); L = t₁−t₀+1 is the rung count so L−1 = t₁−t₀;
  integer conventions are explicit (ℤ throughout); the "march gap" g is
  the unique shadow gap met by the rung-window union.

  Lean 4.34.1 / Mathlib (pin d13f23b723b8a846827a245b89c10fc7d3f11612).
  Zero sorrys. Standard axioms only.
-/

import Mathlib

namespace MarchLadderCeiling

/-- One-sided ladder ceiling (the arithmetic core of R259's proof, reviewer
    checks §2–§5: window union, gap-meeting, neighbor exclusion, integer
    rounding). Rung interval [t₀,t₁] (integers, t₀ ≤ t₁); the rung windows
    [1−s, 184−s], s ∈ [t₀,t₁], have union [1−t₁, 184−t₀]; that union meets
    the shadow-gap set G in exactly {g}; gprev, gnext ∈ G flank g.
    Conclusion: t₁−t₀ ≤ (gnext−gprev) − 185. -/
theorem one_sided_ceiling (t₀ t₁ g gprev gnext : ℤ) (G : Set ℤ)
    (hI : t₀ ≤ t₁)
    (hg : g ∈ G) (hprev : gprev ∈ G) (hnext : gnext ∈ G)
    (hlt : gprev < g) (hgt : g < gnext)
    (hmeet : (Set.Icc (1 - t₁) (184 - t₀) ∩ G) = {g}) :
    t₁ - t₀ ≤ (gnext - gprev) - 185 := by
  have hgmem : g ∈ Set.Icc (1 - t₁) (184 - t₀) ∩ G := by
    rw [hmeet]; rfl
  have hglo : 1 - t₁ ≤ g := (Set.mem_Icc.mp hgmem.1).1
  have hghi : g ≤ 184 - t₀ := (Set.mem_Icc.mp hgmem.1).2
  -- Neighbor exclusion: gprev < 1−t₁ and gnext > 184−t₀ (else the
  -- neighbor would lie in the union, contradicting the singleton meet).
  have hexcl_prev : gprev < 1 - t₁ := by
    by_contra hcon
    push_neg at hcon
    have hmem : gprev ∈ Set.Icc (1 - t₁) (184 - t₀) ∩ G :=
      ⟨Set.mem_Icc.mpr ⟨hcon, by omega⟩, hprev⟩
    rw [hmeet] at hmem
    have heq : gprev = g := Set.mem_singleton_iff.mp hmem
    omega
  have hexcl_next : 184 - t₀ < gnext := by
    by_contra hcon
    push_neg at hcon
    have hmem : gnext ∈ Set.Icc (1 - t₁) (184 - t₀) ∩ G :=
      ⟨Set.mem_Icc.mpr ⟨by omega, hcon⟩, hnext⟩
    rw [hmeet] at hmem
    have heq : gnext = g := Set.mem_singleton_iff.mp hmem
    omega
  -- Integer rounding: t₁ ≤ −gprev and t₀ ≥ 185−gnext; the bound follows.
  omega

/-- R259 Theorem 6 (two-sided ladder ceiling): a single-gap hole-twin
    ladder with L = t₁−t₀+1 rungs, side-A march gap ga flanked by
    gaprev_a/ganext_a and side-B march gap gb flanked by gbprev_b/gbnext_b
    (side B's rung interval [t₀',t₁'] has the same length, per R257's
    characterization over I+δ with δ = ga−gb, cited), satisfies
    L − 1 = t₁−t₀ ≤ min(ganext_a−gaprev_a, gbnext_b−gbprev_b) − 185. -/
theorem theorem6 (t₀ t₁ t₀' t₁' : ℤ)
    (hI : t₀ ≤ t₁) (hlen : t₁' - t₀' = t₁ - t₀)
    (ga gaprev ganext : ℤ) (Ga : Set ℤ)
    (gb gbprev gbnext : ℤ) (Gb : Set ℤ)
    (hga : ga ∈ Ga) (hgaprev : gaprev ∈ Ga) (hganext : ganext ∈ Ga)
    (hgalt : gaprev < ga) (hgagt : ga < ganext)
    (hmeetA : (Set.Icc (1 - t₁) (184 - t₀) ∩ Ga) = {ga})
    (hgb : gb ∈ Gb) (hgbprev : gbprev ∈ Gb) (hgbnext : gbnext ∈ Gb)
    (hgblt : gbprev < gb) (hgbgt : gb < gbnext)
    (hmeetB : (Set.Icc (1 - t₁') (184 - t₀') ∩ Gb) = {gb}) :
    t₁ - t₀ ≤ min (ganext - gaprev) (gbnext - gbprev) - 185 := by
  have hA := one_sided_ceiling t₀ t₁ ga gaprev ganext Ga hI
    hga hgaprev hganext hgalt hgagt hmeetA
  have hI' : t₀' ≤ t₁' := by omega
  have hB := one_sided_ceiling t₀' t₁' gb gbprev gbnext Gb hI'
    hgb hgbprev hgbnext hgblt hgbgt hmeetB
  omega

/-- R263-a, non-binding case (arithmetic piece): with Theorem 6's bound
    t₁−t₀ ≤ min(isoA,isoB)−185 and the cited [COMPUTED] fact that every
    distinct-base ladder-capable pair except the binding (R47#15×R47#21)
    pair has min_iso ≤ 193, a ladder has L−1 ≤ 8, i.e. L ≤ 9. -/
theorem catalog_ceiling_nonbinding (t₀ t₁ isoA isoB : ℤ)
    (hth6 : t₁ - t₀ ≤ min isoA isoB - 185)
    (hbound : min isoA isoB ≤ 193) :
    t₁ - t₀ + 1 ≤ 9 := by
  omega

/-- R263-a, binding-pair case (arithmetic piece): the R47#15 × R47#21
    pair's march hole-runs share exactly 9 consecutive holes
    [COMPUTED] ×2 (r263_ceiling.json vs r263_verify.json); a ladder of
    length L needs L shared consecutive holes, so L ≤ overlap ≤ 9. -/
theorem catalog_ceiling_binding (L overlap : ℤ)
    (hladder : L ≤ overlap)
    (hoverlap : overlap ≤ 9) :
    L ≤ 9 := by
  omega

/-- R263-a (catalog ceiling, arithmetic core — R263's Theorem (R263-a)
    [PROVED*], rule-9 Q-12 conditional SURVIVES via Bunny (ts
    1791673535.102169, 2026-10-10)). Over the 62-center catalog universe
    (62 bases × raw/φ × all valid translates), every single-gap
    hole-twin ladder has length L ≤ 9.

    The hand proof's arithmetic skeleton, with the [COMPUTED] ledger
    facts as hypotheses (cited, not re-proved):
    - no same-base ladder exists (0 mask collisions over all 9,242
      translates × 124 oriented bases) — the `hdata` hypothesis
      quantifies over distinct-base ladder-capable pairs only;
    - max min(iso_X,iso_Y) = 194 over distinct-base ladder-capable
      pairs, attained only by R47#15 × R47#21 (`hdata`, `hbind`);
    - that binding pair's shared overlap is exactly 9 (`hoverlap`).
    L = 9 is attained (R259 ladder 49, holes 19..27) — a cited
    [COMPUTED] datum, not formalized (attainment needs the catalog
    data tables). L ≥ 10 needs a new base outside the catalog. -/
theorem catalog_ceiling (L isoA isoB overlap : ℤ)
    (hth6 : L - 1 ≤ min isoA isoB - 185)
    (hdata : min isoA isoB ≤ 194)
    (hbind : min isoA isoB = 194 → L ≤ overlap)
    (hoverlap : overlap ≤ 9) :
    L ≤ 9 := by
  rcases lt_or_ge (min isoA isoB) 194 with h | h
  · have h193 : min isoA isoB ≤ 193 := by omega
    omega
  · have h194 : min isoA isoB = 194 := by omega
    have hL := hbind h194
    omega

end MarchLadderCeiling
