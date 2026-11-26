import Mathlib.Tactic

namespace Interval3SUM

/-- Even optimizing delta, the guaranteed saving per unit of width exponent
in the original Theorem 5.9 ledger cannot exceed either envelope. -/
theorem old_envelope (u gamma q x : ℚ)
    (terminal : x ≤ u) (pre : x ≤ gamma-u) (ask : x ≤ 1/12-q-u/6) :
    x ≤ gamma/2 ∧ x ≤ (1-12*q)/14 := by
  constructor <;> linarith

theorem old_width_identity (delta : ℚ) (hd : 0 ≤ delta) :
    (1 : ℚ)/(12+2*delta) = (1-2*(delta/(12+2*delta)))/12 := by
  have nz : 12+2*delta ≠ 0 := by linarith
  field_simp
  <;> ring

theorem compare_certified_gaps :
    (3737/10000000 : ℚ) < (3738/10000000 : ℚ) := by norm_num

end Interval3SUM
#print axioms Interval3SUM.old_envelope
#print axioms Interval3SUM.old_width_identity
#print axioms Interval3SUM.compare_certified_gaps
