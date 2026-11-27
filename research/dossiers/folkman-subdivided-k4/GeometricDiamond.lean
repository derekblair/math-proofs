import GeometricPageTransfer

namespace RobustFolkman.GeometricGap
open Matrix
abbrev Four := Fin 2 ⊕ Fin 2

def uniformB (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => t

noncomputable def diamondGram (t r : ℝ) : Matrix Four Four ℝ :=
  anchorBlock (setAnchor t) (uniformB t) r

theorem setAnchor_det (t : ℝ) : (setAnchor t).det=1-t^2 := by
  rw [Matrix.det_fin_two]
  simp [setAnchor,pow_two]

theorem diamondGram_det (t r : ℝ) (t0 : 0<t) (t1 : t<1) :
    (diamondGram t r).det=(1-t^2)*(pageFactor t t^2-(r-2*t^2/(1+t))^2) := by
  have dd : 0<(setAnchor t).det := by
    rw [setAnchor_det]
    have p := mul_pos (sub_pos.mpr t1) (show 0<1+t by positivity)
    nlinarith only [p]
  let _ : Invertible (setAnchor t) := Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr dd.ne')
  let f : Fin 2→ℝ := fun _ => t/(1+t)
  have ff : (setAnchor t) *ᵥ f=fun _ => t := by
    ext i
    fin_cases i <;>
      simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two,setAnchor,f] <;>
      field_simp <;> ring
  have solved : (⅟(setAnchor t))*uniformB t=uniformB (t/(1+t)) := by
    have h : (setAnchor t)*uniformB (t/(1+t))=uniformB t := by
      ext i j
      exact congrFun ff i
    rw [←h,←Matrix.mul_assoc,invOf_mul_self,Matrix.one_mul]
  have prod (a b : Fin 2) :
      ((uniformB t).transpose*⅟(setAnchor t)*uniformB t) a b=2*t^2/(1+t) := by
    rw [Matrix.mul_assoc,solved,Matrix.mul_apply]
    simp [uniformB,Fin.sum_univ_two]
    ring
  rw [diamondGram,anchor_det,setAnchor_det,prod,prod,prod,prod]
  simp [pageFactor,pow_two]

theorem diamondGram_upper (t r : ℝ) (t0 : 0<t) (t1 : t<1) :
    (diamondGram t r).det≤(1-t^2)*pageFactor t t^2 := by
  rw [diamondGram_det t r t0 t1]
  have a : 0≤1-t^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr t1.le) (show 0≤1+t by positivity)]
  exact mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg _)) a

#print axioms diamondGram_det
end RobustFolkman.GeometricGap
