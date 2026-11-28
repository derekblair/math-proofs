import BoxExit
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card

open scoped BigOperators
namespace DirectedBoxDSP

variable {F E K : Type*} [Fintype F] [DecidableEq E]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- For every surviving cut face, the ancestor's count includes the
segments meeting that face in the descendant. Original uncropped
faces cannot exclude an endpoint. Count arcs, not incidences at corners. -/
theorem inherited_boundary_budget
    (boundary : Finset E) (active : Finset F) (counted : F → Finset E)
    (a b : E → F → K) (cap : F → K) (B : ℕ)
    (enter : ∀ e ∈ boundary, ∀ f, a e f < cap f)
    (leave : ∀ e ∈ boundary, ∃ f, cap f < b e f)
    (root : ∀ e ∈ boundary, ∀ f ∉ active, b e f ≤ cap f)
    (charge : ∀ e ∈ boundary, ∀ f ∈ active, ∀ t : K, 0 < t → t < 1 →
      (∀ g, a e g + t * (b e g - a e g) ≤ cap g) →
      a e f + t * (b e f - a e f) = cap f → e ∈ counted f)
    (budget : ∀ f ∈ active, (counted f).card ≤ B) :
    boundary.card ≤ active.card * B := by
  classical
  have hs : boundary ⊆ active.biUnion counted := by
    intro e he
    obtain ⟨t, h0, h1, hin, f, hfout, hfeq⟩ :=
      finite_halfspace_exit (a e) (b e) cap (enter e he) (leave e he)
    have hf : f ∈ active := by
      by_contra hn
      exact not_lt_of_ge (root e he f hn) hfout
    exact Finset.mem_biUnion.mpr ⟨f, hf, charge e he f hf t h0 h1 hin hfeq⟩
  calc
    boundary.card ≤ (active.biUnion counted).card := Finset.card_le_card hs
    _ ≤ ∑ f ∈ active, (counted f).card := Finset.card_biUnion_le
    _ ≤ ∑ _f ∈ active, B := Finset.sum_le_sum budget
    _ = active.card * B := by simp

/-- A face introduced by an earlier cut retains the cut's coordinate
level. Tightening other coordinate bounds cannot remove the ancestor's
obligation to count its intersections. -/
theorem ancestor_boundary_budget
    (boundary : Finset E) (active : Finset F) (counted : F → Finset E)
    (a b : E → F → K) (cap : F → K)
    (ancestor : F → F → K) (B : ℕ)
    (enter : ∀ e ∈ boundary, ∀ f, a e f < cap f)
    (leave : ∀ e ∈ boundary, ∃ f, cap f < b e f)
    (root : ∀ e ∈ boundary, ∀ f ∉ active, b e f ≤ cap f)
    (nested : ∀ f ∈ active, ∀ g, cap g ≤ ancestor f g)
    (charge : ∀ e ∈ boundary, ∀ f ∈ active, ∀ t : K, 0 < t → t < 1 →
      (∀ g, a e g + t * (b e g - a e g) ≤ ancestor f g) →
      a e f + t * (b e f - a e f) = cap f → e ∈ counted f)
    (budget : ∀ f ∈ active, (counted f).card ≤ B) :
    boundary.card ≤ active.card * B := by
  refine inherited_boundary_budget boundary active counted a b cap B enter leave root ?_ budget
  intro e he f hf t h0 h1 hin hface
  exact charge e he f hf t h0 h1 (fun g => (hin g).trans (nested f hf g)) hface

#print axioms ancestor_boundary_budget
#print axioms inherited_boundary_budget
end DirectedBoxDSP
