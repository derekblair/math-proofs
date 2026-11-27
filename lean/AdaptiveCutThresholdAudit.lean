import Mathlib.Tactic

/-! Exact rational margins for the sparse-edit threshold. -/

namespace AdaptiveCutThresholdAudit

def a : ℚ := 161/125
def δ : ℚ := 511/20000
def κ : ℚ := 17/1000
def x : ℚ := (a-1)^2
def q : ℚ := 27/(16*a^2*(1-x))-1

theorem cap_domain : 0 < x ∧ x < 1 ∧ 0 < q := by
  norm_num [q, x, a]

theorem sparse_margin : 3*κ < 2*δ := by norm_num [κ, δ]

theorem short_margin : 2*δ < (q-q^2/2)/2 := by
  norm_num [δ, q, x, a]

theorem long_margin : δ+κ < x/2+x^2/4 := by
  norm_num [δ, κ, x, a]

theorem cap_monotone_margin : (a-1)*(2*a-1) < 1 := by norm_num [a]

#print axioms cap_domain
#print axioms sparse_margin
#print axioms short_margin
#print axioms long_margin
#print axioms cap_monotone_margin
end AdaptiveCutThresholdAudit
