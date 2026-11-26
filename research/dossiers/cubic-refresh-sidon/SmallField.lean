import Mathlib.Algebra.Field.Basic

namespace SmallField
variable {F : Type*} [Field F]

/-- Evaluating a candidate span relation at two roots forces incompatible
coefficients on the other root polynomial in the disjoint-pair case. -/
theorem pair_offset_obstruction {a b P v : F}
    (hab : a ≠ b) (hP : P ≠ 0)
    (ha : v = (P * a)⁻¹) (hb : v = (P * b)⁻¹) : False := by
  apply hab
  apply mul_left_cancel₀ hP
  simpa only [inv_inv] using congrArg (fun x : F => x⁻¹) (ha.symm.trans hb)

/-- Two monic quadratics span at most a line of degree-at-most-one
polynomials: elements of that intersection are multiples of their difference
when represented by their coefficients. -/
theorem monic_span_low (r0 r1 s0 s1 u v : F) (h : u + v = 0) :
    (u*r0 + v*s0, u*r1 + v*s1) = (u*(r0-s0),u*(r1-s1)) := by
  have hv : v = -u := by
    have hc := congrArg (fun z : F => z - u) h
    simpa [add_comm u v, sub_eq_add_neg, add_assoc] using hc
  subst v
  simp [mul_add, sub_eq_add_neg]

#print axioms pair_offset_obstruction
#print axioms monic_span_low
end SmallField
