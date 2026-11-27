import GeometricPatternDet
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace RobustFolkman.GeometricGap
open Matrix

noncomputable def patternRate {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℝ) : ℝ := -(Real.log M.det)/2

noncomputable def capRate (t : ℝ) : ℝ :=
  -(Real.log (1-(t/(1+t))^2))/2

/-- The exact five maximized Gram determinant rates give the full
strict density window in the geometric construction. -/
theorem exact_pattern_rate_window (t : ℝ) (t0 : 0<t) (ts : t≤1/20000)
    (E : Matrix (Fin 2) (Fin 2) ℝ)
    (T : Matrix (Fin 2⊕Unit) (Fin 2⊕Unit) ℝ)
    (D : Matrix Four Four ℝ) (H : Matrix Five Five ℝ)
    (J : Matrix (Five⊕Unit) (Five⊕Unit) ℝ)
    (e : GramOptimal edgeCon t E) (tr : GramOptimal triangleCon t T)
    (d : GramOptimal diamondEdges t D) (h : GramOptimal subEdges t H)
    (j : GramOptimal extCon t J) :
    (patternRate T-patternRate E=patternRate E+capRate t) ∧
    ∃ x : ℝ, 0<x ∧ patternRate T-patternRate E<x ∧
      2*x<patternRate H-patternRate T ∧ 3*x<patternRate J-patternRate T ∧
      patternRate T<3*x ∧ 2*patternRate T-patternRate D<2*x := by
  classical
  obtain ⟨Ee,Te,De,Hlt,Je⟩ := exact_pattern_determinants t t0 ts E T D H J e tr d h j
  let f := pageFactor t t
  let L := -(Real.log f)/2
  have fp : 0<f := by
    have k := centered_less t0 (show t≤1/2 by linarith only [ts])
    dsimp [f,pageFactor]
    linarith only [k,ts]
  have Ep : 0<E.det := by
    rw [Ee]
    have z := mul_pos (show 0<1-t by linarith only [ts]) (show 0<1+t by positivity)
    nlinarith only [z]
  have Hp : 0<H.det :=
    (optimum_is_localized subEdges subEdges_sym (by decide) t t0 ts H h.1 h.2).1.det_pos
  have fe : f<E.det := Ee.symm ▸ page_strictly_smaller_than_edge t t0 (by linarith only [ts])
  have f1 : f<1 := fe.trans_le (by rw [Ee]; nlinarith only [sq_nonneg t])
  have lp : 0<L := by dsimp [L]; linarith only [Real.log_neg fp f1]
  have el : patternRate E<L := by
    dsimp [patternRate,L]
    linarith only [Real.log_lt_log fp fe]
  have tR : patternRate T=patternRate E+L := by
    unfold patternRate
    rw [Te,Real.log_mul Ep.ne' fp.ne']
    dsimp [L,f]
    ring
  have dR : patternRate D=patternRate E+2*L := by
    unfold patternRate
    rw [De,Real.log_mul Ep.ne' (pow_ne_zero _ fp.ne'),Real.log_pow]
    dsimp [L,f]
    ring
  have jR : patternRate J=patternRate H+L := by
    unfold patternRate
    rw [Je,Real.log_mul Hp.ne' fp.ne']
    dsimp [L,f]
    ring
  have hR : patternRate E+3*L < patternRate H := by
    have q := Real.log_lt_log Hp Hlt
    rw [Real.log_mul Ep.ne' (pow_ne_zero _ fp.ne'),Real.log_pow] at q
    dsimp [patternRate,L,f]
    norm_num at q
    linarith only [q]
  constructor
  · have ee : f/E.det=1-(t/(1+t))^2 := Ee.symm ▸ effective_cap_page t t0 (by linarith only [ts])
    rw [tR]
    unfold capRate patternRate
    rw [←ee,Real.log_div fp.ne' Ep.ne']
    dsimp [L]
    ring
  · rw [tR,dR,jR]
    have q : patternRate E+L-patternRate E=L := by ring
    rw [q]
    exact exact_rate_window (patternRate E) L (patternRate H) lp el hR

#print axioms exact_pattern_rate_window
end RobustFolkman.GeometricGap
