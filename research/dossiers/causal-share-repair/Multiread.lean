import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Polynomial

namespace Multiread

variable {F : Type*} [Field F]

/-- A degree-d rational numerator / denominator pair cannot take one
value on more than d distinct points away from poles, unless its numerator
is actually the corresponding multiple of its denominator. -/
theorem constant_fiber_bound (N D : F[X]) (c : F) (d : ℕ)
    (nD : N.natDegree ≤ d) (dD : D.natDegree ≤ d)
    (unequal : N - C c * D ≠ 0) (sites : Finset F)
    (same : ∀ x ∈ sites, N.eval x = c * D.eval x) : sites.card ≤ d := by
  have deg : (N - C c * D).natDegree ≤ d := by
    have cp : (C c * D).natDegree ≤ d := by
      calc
        _ ≤ (C c).natDegree + D.natDegree := natDegree_mul_le
        _ = D.natDegree := by simp
        _ ≤ d := dD
    exact (natDegree_sub_le _ _).trans (max_le nD cp)
  apply le_trans ?_ deg
  apply Polynomial.card_le_degree_of_subset_roots
  intro x hx
  apply (Polynomial.mem_roots unequal).2
  simp [same x hx]

/-- A surviving nonzero residue at zero prevents the identically constant case. -/
theorem pole_nonconstant (N D : F[X]) (c : F) (n0 : N.eval 0 ≠ 0)
    (d0 : D.eval 0 = 0) : N - C c * D ≠ 0 := by
  intro zero
  apply n0
  have h := congrArg (Polynomial.eval 0) zero
  simpa [d0] using h

theorem ratio_edge_form (a b u v : F) (hu : b-u ≠ 0) (hv : b-v ≠ 0) :
    (a-u)/(b-u) - (a-v)/(b-v) = ((a-b)*(u-v))/((b-u)*(b-v)) := by
  field_simp [hu,hv]
  ring

#print axioms constant_fiber_bound
#print axioms pole_nonconstant
#print axioms ratio_edge_form

end Multiread
