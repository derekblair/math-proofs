import Mathlib.Tactic

namespace Interval3SUM

/-- Exponent inequalities; log/entropy bounds for the last three inputs
are independently enclosed in exact rational intervals, not in this file. -/
theorem budget (gamma query radius : ℚ)
    (G : 99732/10000000 ≤ gamma) (Q : query ≤ 779292/10000000)
    (R : 490952/10000000 ≤ radius) :
    2*(6012/100000 : ℚ) < (12+6012/100000)*gamma ∧
    6012/100000+(12+6012/100000)*query<1 ∧
    (407/100000)*(12+6012/100000)<radius ∧
    2-(6012/100000 : ℚ)*(407/100000) < 19997554/10000000 := by
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith only [G]
  · nlinarith only [Q]
  · nlinarith only [R]
  · norm_num

theorem five_term_budget (gamma query radius : ℚ)
    (G : 1027149/100000000 ≤ gamma) (Q : query ≤ 7776831/100000000)
    (R : 7282536/100000000 ≤ radius) :
    2*(6193/100000 : ℚ) < (12+6193/100000)*gamma ∧
    6193/100000+(12+6193/100000)*query<1 ∧
    (60375/10000000)*(12+6193/100000)<radius ∧
    2-(6193/100000 : ℚ)*(60375/10000000) < 19996262/10000000 := by
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith only [G]
  · nlinarith only [Q]
  · nlinarith only [R]
  · norm_num

end Interval3SUM
#print axioms Interval3SUM.budget
#print axioms Interval3SUM.five_term_budget
