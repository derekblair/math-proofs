import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Lean.Elab.Tactic.Omega

open scoped BigOperators
namespace Erdős151.H12

variable {V : Type*}

/-- In an edge-minimal Ramsey core the summed link size is at least
three halves the summed degree. Under the 8/9 degree frontier at
order 54, this can only happen by equality everywhere. -/
theorem core_average_n54 (C : Finset V) (deg link : V → Nat)
    (hdeg : ∀ v ∈ C, deg v = 8 ∨ deg v = 9)
    (h8 : ∀ v ∈ C, deg v = 8 → link v ≤ 12)
    (h9 : ∀ v ∈ C, deg v = 9 → link v ≤ 13)
    (hdensity : 3*(∑ v ∈ C, deg v) ≤ 2*(∑ v ∈ C, link v)) :
    ∀ v ∈ C, deg v = 8 ∧ link v = 12 := by
  classical
  have pt (v : V) (hv : v ∈ C) : 2*link v ≤ 3*deg v := by
    rcases hdeg v hv with ha|ha
    · have := h8 v hv ha; omega
    · have := h9 v hv ha; omega
  have eq (v : V) (hv : v ∈ C) : 2*link v = 3*deg v := by
    by_contra hn
    have st : 2*link v < 3*deg v := lt_of_le_of_ne (pt v hv) hn
    have slt := Finset.sum_lt_sum pt ⟨v,hv,st⟩
    rw [← Finset.mul_sum, ← Finset.mul_sum] at slt
    exact (not_lt_of_ge hdensity) slt
  intro v hv
  have h := eq v hv
  rcases hdeg v hv with ha|ha
  · omega
  · have := h9 v hv ha; omega

/-- A compact formulation of the unified order-at-least-53 frontier.
Every degree-eight core has at most twelve link edges, and each degree
step above eight grants at most one additional link edge. Global
density rules out any strict loss. -/
theorem core_average_of_link_bound (C : Finset V) (deg link : V → Nat)
    (minD : ∀ v ∈ C, 8 ≤ deg v)
    (hlink : ∀ v ∈ C, link v ≤ deg v + 4)
    (hdensity : 3*(∑ v ∈ C, deg v) ≤ 2*(∑ v ∈ C, link v)) :
    ∀ v ∈ C, deg v = 8 ∧ link v = 12 := by
  classical
  have pt (v : V) (hv : v ∈ C) : 2*link v ≤ 3*deg v := by
    have h1 := minD v hv
    have h2 := hlink v hv
    omega
  intro v hv
  have e : 2*link v = 3*deg v := by
    by_contra hn
    have st := lt_of_le_of_ne (pt v hv) hn
    have slt := Finset.sum_lt_sum pt ⟨v,hv,st⟩
    rw [← Finset.mul_sum, ← Finset.mul_sum] at slt
    exact (not_lt_of_ge hdensity) slt
  have hm := minD v hv
  have hl := hlink v hv
  omega

#print axioms core_average_of_link_bound
#print axioms core_average_n54
end Erdős151.H12
