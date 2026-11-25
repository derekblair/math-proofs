/-
  SigmaTrans.lean — R275 σ-transfer: Pareto-min ascent-transfer machinery, no-forcing theorems (Q-22 scoped bar).

  Paper: papers/sigma-transfer-fiber-overlap-October-11-2026/
  Status: [PROVED] — A3_holds, no_forcing_equality/disjoint/sharing (+ transfer API)
  Verification: Lean 4.34.1 + Mathlib v4.34.1 (pinned d13f23b); R310: bakkie full-library build exit 0, zero sorrys, axioms standard-only.
-/

/-
  SigmaTrans.lean — Lean formalization of R275's σ-spectrum transition theorems
  (T5 transition locality, T6 no-forcing models, T7′ dual e-min, T8′ no
  cotransition, demoter existence, transition-DAG determinism).

  Source: ~/workspace/math-unsolved/ROUND275_DOSSIER.md (Round 275, 2026-10-10).
  Rule-9 hostile review Q-22: quoted "SURVIVES" (scoped) 2026-10-10 21:31 PDT.
  Scoped bar (Q-22): T5 = old-spectrum queries (each class's transition status
  is a function of per-class down-set queries on the two spectra); T6 =
  abstract A1–A3 only (three explicit models as Lean-checked existence
  statements); T2′/T7′/T8′ = full-normalized-universe + witness-level
  reflection (abstract reflection endomap with s-preservation; σ-internality
  is captured by r being an endomap on the class universe).

  Honesty labels:
  - status_local (T5), demoter_exists, dag_deterministic, dual_emin (T7′),
    no_cotransition (T8′), no_forcing_{equality,disjoint,sharing} (T6):
    [PROVED*] (proofs below, Lean-checked).
  - The 103-pair transition census, 558-case T5 down-set audit, T6 model
    audits, T2′/T7′/T8′ scripted audits: [COMPUTED]×2 data — cited from the
    dossier, never re-claimed here.
  - Target 7 `reflection_per_shape` (T2′ per-shape, needs the (S,E) evaluator
    formalized): DEFERRED (flagged heavier in the dossier) — not attempted.
  - R273's original T2 census-universe conclusion is FALSE ([COMPUTED]
    decisive); the T2 universe-membership gap lives in the Q-19 review spec,
    not here.

  Lean 4.34.1 / Mathlib (pin d13f23b723b8a846827a245b89c10fc7d3f11612).
  Zero sorrys. Standard axioms only.
-/

import Mathlib

namespace SigmaTrans

/-- The ≤-Pareto frontier: minimal elements of a finite set of (e,s) classes. -/
def paretoMin (S : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  S.filter (fun p => ∀ q ∈ S, q ≤ p → q = p)

/-- The down-set of c in S — the "old-spectrum query" at c. -/
def downSet (S : Finset (ℕ × ℕ)) (c : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  S.filter (· ≤ c)

/-- Pareto membership in down-set-query form: c is Pareto iff it is present
    and its down-set is the singleton {c}. -/
theorem mem_paretoMin_iff (S : Finset (ℕ × ℕ)) (c : ℕ × ℕ) :
    c ∈ paretoMin S ↔ c ∈ S ∧ downSet S c = {c} := by
  constructor
  · intro h
    rw [paretoMin, Finset.mem_filter] at h
    refine ⟨h.1, ?_⟩
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨Finset.mem_filter.mpr ⟨h.1, le_rfl⟩, fun x hx => ?_⟩
    rw [downSet, Finset.mem_filter] at hx
    exact h.2 x hx.1 hx.2
  · rintro ⟨hcS, hds⟩
    rw [paretoMin, Finset.mem_filter]
    refine ⟨hcS, fun q hqS hqc => ?_⟩
    have hq : q ∈ downSet S c := Finset.mem_filter.mpr ⟨hqS, hqc⟩
    rw [hds, Finset.mem_singleton] at hq
    exact hq

/-- Transition statuses (R275 §1 taxonomy over an adjacent pair σ→σ+1). -/
inductive Status : Type
  | persist | demoted | extinct | fresh | promoted
  deriving DecidableEq, Repr

/-- Transition status of class c across σ→σ+1, computed from the two spectra. -/
def transStatus (S S' : Finset (ℕ × ℕ)) (c : ℕ × ℕ) : Status :=
  if c ∈ paretoMin S then
    if c ∈ paretoMin S' then .persist
    else if c ∈ S' then .demoted
    else .extinct
  else if c ∈ paretoMin S' then
    if c ∈ S then .promoted
    else .fresh
  else .fresh

/-- T5 (transition locality): the transition status is a function of per-class
    down-set queries on the two spectra — the "old-spectrum query" form. -/
theorem status_local (S S' : Finset (ℕ × ℕ)) (c : ℕ × ℕ) :
    transStatus S S' c =
      (if c ∈ S ∧ downSet S c = {c} then
        if c ∈ S' ∧ downSet S' c = {c} then Status.persist
        else if c ∈ S' then Status.demoted
        else Status.extinct
      else if c ∈ S' ∧ downSet S' c = {c} then
        if c ∈ S then Status.promoted
        else Status.fresh
      else Status.fresh) := by
  unfold transStatus
  simp only [mem_paretoMin_iff]

/-- The transition-status function is well-defined and total; the five
    statuses are exhaustive over the classified domain Π(S) ∪ Π(S′). -/
theorem dag_deterministic (S S' : Finset (ℕ × ℕ)) :
    ∀ c ∈ paretoMin S ∪ paretoMin S',
      transStatus S S' c = .persist ∨ transStatus S S' c = .demoted ∨
      transStatus S S' c = .extinct ∨ transStatus S S' c = .fresh ∨
      transStatus S S' c = .promoted := by
  intro c _
  by_cases hP : c ∈ paretoMin S <;> by_cases hP' : c ∈ paretoMin S' <;>
    by_cases hS : c ∈ S <;> by_cases hS' : c ∈ S' <;>
    simp [transStatus, hP, hP', hS, hS']

/-- Demoter existence (finite descent): a non-Pareto class of S′ is strictly
    dominated by a Pareto class of S′ (demote edges are orientation-audited). -/
theorem demoter_exists (S : Finset (ℕ × ℕ)) (c : ℕ × ℕ) (hc : c ∈ S)
    (hnp : c ∉ paretoMin S) : ∃ q ∈ paretoMin S, q ≤ c ∧ q ≠ c := by
  have hne : ∃ q ∈ S, q ≤ c ∧ q ≠ c := by
    have h2 := hnp
    rw [paretoMin, Finset.mem_filter] at h2
    push Not at h2
    exact h2 hc
  -- T = {q ∈ S : q ≤ c, q ≠ c} is nonempty; take a (e+s)-minimal element.
  set T : Finset (ℕ × ℕ) := S.filter (fun q => q ≤ c ∧ q ≠ c) with hTdef
  have hTne : T.Nonempty := by
    obtain ⟨q, hqS, hqc, hqne⟩ := hne
    exact ⟨q, by rw [hTdef]; exact Finset.mem_filter.mpr ⟨hqS, hqc, hqne⟩⟩
  obtain ⟨q, hqT, hqmin⟩ := Finset.exists_min_image T (fun q => q.1 + q.2) hTne
  rw [hTdef, Finset.mem_filter] at hqT
  obtain ⟨hqS, hqc, hqne⟩ := hqT
  by_cases hqP : q ∈ paretoMin S
  · exact ⟨q, hqP, hqc, hqne⟩
  · exfalso
    have h3 := hqP
    rw [paretoMin, Finset.mem_filter] at h3
    push Not at h3
    obtain ⟨r, hrS, hrq, hrne⟩ := h3 hqS
    have hrT : r ∈ T := by
      rw [hTdef]
      refine Finset.mem_filter.mpr ⟨hrS, le_trans hrq hqc, ?_⟩
      intro heq
      apply hqne
      rw [heq] at hrq
      exact le_antisymm hqc hrq
    have hlt : r.1 + r.2 < q.1 + q.2 := by
      rw [Prod.le_def] at hrq
      have hne' : r.1 ≠ q.1 ∨ r.2 ≠ q.2 := by
        by_contra hcon
        push Not at hcon
        apply hrne
        exact Prod.ext hcon.1 hcon.2
      omega
    have hle := hqmin r hrT
    omega

/-- T7′ (dual e-min, witness-level reflection): a Pareto class's in-universe
    dual cannot strictly dominate it — s-preservation forces e′ ≥ e. -/
theorem dual_emin (S : Finset (ℕ × ℕ)) (r : ℕ × ℕ → ℕ × ℕ)
    (hs : ∀ p, (r p).2 = p.2) (p : ℕ × ℕ)
    (hP : p ∈ paretoMin S) (hd : r p ∈ S) : p.1 ≤ (r p).1 := by
  by_contra hlt
  push Not at hlt
  have hle : r p ≤ p := by
    rw [Prod.le_def]
    exact ⟨by omega, by rw [hs p]⟩
  have hne : r p ≠ p := by
    intro heq
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  have h2 := hP
  rw [paretoMin, Finset.mem_filter] at h2
  exact absurd (h2.2 (r p) hd hle) hne

/-- T8′ (no cotransition): the dual of a Pareto class is never a distinct
    Pareto class — it is either self-dual or non-Pareto. -/
theorem no_cotransition (S : Finset (ℕ × ℕ)) (r : ℕ × ℕ → ℕ × ℕ)
    (hs : ∀ p, (r p).2 = p.2) (p : ℕ × ℕ)
    (hP : p ∈ paretoMin S) (hdP : r p ∈ paretoMin S) : r p = p := by
  have hdS : r p ∈ S := by
    rw [paretoMin, Finset.mem_filter] at hdP
    exact hdP.1
  have hle : p ≤ r p := by
    have h := dual_emin S r hs p hP hdS
    rw [Prod.le_def]
    exact ⟨h, by rw [hs p]⟩
  have h2 := hdP
  rw [paretoMin, Finset.mem_filter] at h2
  have hpS : p ∈ S := by
    rw [paretoMin, Finset.mem_filter] at hP
    exact hP.1
  exact (h2.2 p hpS hle).symm

/-- The E-floor function (T1): floor(σ) = max(0, 183 − 2σ), ℕ-truncated. -/
def floor (σ : ℕ) : ℕ := 183 - 2 * σ

/-- A1 (floor axiom): every class of S has e ≥ fl. -/
def A1 (S : Finset (ℕ × ℕ)) (fl : ℕ) : Prop := ∀ p ∈ S, fl ≤ p.1

/-- A2 (reflection-closure axiom): the reflected e-value appears at the same s. -/
def A2 (S : Finset (ℕ × ℕ)) (r : ℕ × ℕ → ℕ × ℕ) : Prop :=
  ∀ p ∈ S, ∃ q ∈ S, (r p).1 = q.1 ∧ q.2 = p.2

/-- A3 (Pareto axiom): Π(S) is the ≤-minimal set — definitional, always holds. -/
def A3 (S : Finset (ℕ × ℕ)) : Prop := ∀ p ∈ paretoMin S, ∀ q ∈ S, q ≤ p → q = p

theorem A3_holds (S : Finset (ℕ × ℕ)) : A3 S := by
  intro p hp q hqS hqp
  rw [paretoMin, Finset.mem_filter] at hp
  exact hp.2 q hqS hqp

/-- T6, equality model: S = S′ = {(m,0)} satisfies A1–A3, and the two
    frontiers coincide — equality is consistent with the axioms. -/
theorem no_forcing_equality (sa sb m : ℕ) (hm : floor sa ≤ m ∧ floor sb ≤ m) :
    A1 {(m, 0)} (floor sa) ∧ A1 {(m, 0)} (floor sb) ∧ A2 {(m, 0)} id ∧
      paretoMin {(m, 0)} = paretoMin {(m, 0)} := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · intro p hp
    rw [Finset.mem_singleton] at hp
    rw [hp]
    exact hm.1
  · intro p hp
    rw [Finset.mem_singleton] at hp
    rw [hp]
    exact hm.2
  · intro p hp
    exact ⟨p, hp, rfl, rfl⟩

/-- T6, disjoint model: S = {(m,0)}, S′ = {(m,1)} satisfies A1–A3, and the
    frontiers are disjoint — disjointness is consistent with the axioms. -/
theorem no_forcing_disjoint (sa sb m : ℕ) (hm : floor sa ≤ m ∧ floor sb ≤ m) :
    A1 {(m, 0)} (floor sa) ∧ A1 {(m, 1)} (floor sb) ∧ A2 {(m, 0)} id ∧
      A2 {(m, 1)} id ∧ Disjoint (paretoMin {(m, 0)}) (paretoMin {(m, 1)}) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_singleton] at hp
    rw [hp]
    exact hm.1
  · intro p hp
    rw [Finset.mem_singleton] at hp
    rw [hp]
    exact hm.2
  · intro p hp
    exact ⟨p, hp, rfl, rfl⟩
  · intro p hp
    exact ⟨p, hp, rfl, rfl⟩
  · rw [Finset.disjoint_left]
    intro a ha hb
    rw [paretoMin, Finset.mem_filter] at ha hb
    have e1 : a = (m, 0) := Finset.mem_singleton.mp ha.1
    have e2 : a = (m, 1) := Finset.mem_singleton.mp hb.1
    rw [e1] at e2
    simp at e2

/-- T6, sharing model: S = S′ = {(m,1),(m+1,0)} (an antichain) satisfies
    A1–A3, and the two frontiers coincide with 2 elements — sharing is
    consistent with the axioms. -/
theorem no_forcing_sharing (sa sb m : ℕ) (hm : floor sa ≤ m ∧ floor sb ≤ m) :
    A1 {(m, 1), (m + 1, 0)} (floor sa) ∧ A1 {(m, 1), (m + 1, 0)} (floor sb) ∧
      A2 {(m, 1), (m + 1, 0)} id ∧
      paretoMin {(m, 1), (m + 1, 0)} = {(m, 1), (m + 1, 0)} ∧
      (paretoMin {(m, 1), (m + 1, 0)}).card = 2 := by
  have hmin : paretoMin {(m, 1), (m + 1, 0)} = {(m, 1), (m + 1, 0)} := by
    apply Finset.filter_true_of_mem
    intro q hq r hr hle
    rw [Finset.mem_insert, Finset.mem_singleton] at hq hr
    rcases hq with rfl | rfl <;> rcases hr with rfl | rfl
    · rfl
    · rw [Prod.le_def] at hle
      omega
    · rw [Prod.le_def] at hle
      omega
    · rfl
  refine ⟨?_, ?_, ?_, hmin, ?_⟩
  · intro p hp
    rw [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact hm.1
    · show floor sa ≤ m + 1
      have h1 := hm.1
      omega
  · intro p hp
    rw [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact hm.2
    · show floor sb ≤ m + 1
      have h2 := hm.2
      omega
  · intro p hp
    exact ⟨p, hp, rfl, rfl⟩
  · rw [hmin, Finset.card_insert_of_notMem (by simp), Finset.card_singleton]

end SigmaTrans
