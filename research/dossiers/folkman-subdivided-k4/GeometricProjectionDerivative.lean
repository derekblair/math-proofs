import GeometricProjectionJacDet
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace RobustFolkman.GeometricGap
open Matrix ContinuousLinearMap
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Split (I : Type*) := (I ⊕ Unit) → ℝ

def splitRad (z : Split I) := z (.inr ())
def splitVec (z : Split I) : I → ℝ := fun i => z (.inl i)
noncomputable def splitRest (z : Split I) := 1-∑ i, splitVec z i ^ 2
noncomputable def splitPolar (z : Split I) : Split I :=
  Sum.elim (fun i => splitRad z * splitVec z i)
    (fun _ => splitRad z * Real.sqrt (splitRest z))

noncomputable def polarMat (z : Split I) : Matrix (I ⊕ Unit) (I ⊕ Unit) ℝ :=
  Matrix.fromBlocks (splitRad z • (1 : Matrix I I ℝ)) (pageCol (splitVec z))
    (fun _ i => -(splitRad z/Real.sqrt (splitRest z))*splitVec z i)
    (fun _ _ => Real.sqrt (splitRest z))

noncomputable def polarDeriv (z : Split I) : Split I →L[ℝ] Split I :=
  LinearMap.toContinuousLinearMap (polarMat z).toLin'

theorem splitPolar_derivative (z : Split I) (h : 0 < splitRest z) :
    HasFDerivAt splitPolar (polarDeriv z) z := by
  let P (i : I ⊕ Unit) : Split I →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hrad : HasFDerivAt splitRad (P (.inr ())) z := hasFDerivAt_apply _ _
  have hvec (i : I) : HasFDerivAt (fun y => splitVec y i) (P (.inl i)) z :=
    hasFDerivAt_apply _ _
  have hsum : HasFDerivAt (fun y : Split I => ∑ i, splitVec y i ^ 2)
      (∑ i, (2*splitVec z i) • P (.inl i)) z := by
    apply HasFDerivAt.fun_sum
    intro i _
    simpa using (hvec i).pow 2
  have hs : HasFDerivAt (fun y => Real.sqrt (splitRest y))
      ((1/(2*Real.sqrt (splitRest z))) •
        (0-∑ i, (2*splitVec z i) • P (.inl i))) z := by
    exact ((hasFDerivAt_const (c:=1) z).sub hsum).sqrt h.ne'
  apply hasFDerivAt_pi''
  intro i
  cases i with
  | inl i =>
    refine (hrad.mul (hvec i)).congr_fderiv ?_
    apply ContinuousLinearMap.ext
    intro v
    simp [polarDeriv, polarMat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Matrix.fromBlocks, splitRad, splitVec, pageCol, Matrix.one_apply, P]
    <;> ring
  | inr u =>
    cases u
    refine (hrad.mul hs).congr_fderiv ?_
    apply ContinuousLinearMap.ext
    intro v
    simp [polarDeriv, polarMat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Matrix.fromBlocks, splitRad, splitVec, pageCol, P]
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have s0 := (Real.sqrt_pos.2 h).ne'
    field_simp
    <;> ring

theorem splitPolar_derivative_det (z : Split I) (h : 0 < splitRest z) :
    (polarDeriv z).det = (splitRad z)^(Fintype.card I)/Real.sqrt (splitRest z) := by
  unfold polarDeriv
  rw [LinearMap.det_toContinuousLinearMap]
  rw [← LinearMap.det_toMatrix',LinearMap.toMatrix'_toLin']
  apply projection_jacobian_det
  · exact (Real.sqrt_pos.2 h).ne'
  · rw [Real.sq_sqrt h.le]
    unfold splitRest
    ring

#print axioms splitPolar_derivative
#print axioms splitPolar_derivative_det
end RobustFolkman.GeometricGap
