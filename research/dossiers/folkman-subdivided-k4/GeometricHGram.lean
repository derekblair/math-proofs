import GeometricGap
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace RobustFolkman.GeometricGap

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Correlation matrix of H after fixing its seven edge entries at t and
averaging over the swaps of its two tips and its two spine endpoints. -/
def hGram (t r s : K) : Matrix (Fin 5) (Fin 5) K :=
  Matrix.of ![![1,t,t,t,s],![t,1,t,t,s],![t,t,1,r,t],![t,t,r,1,t],![s,s,t,t,1]]

private theorem skip_2_0_0 : (0:Fin 2).succAbove (0:Fin 1) = 1 := by decide
private theorem skip_2_1_0 : (1:Fin 2).succAbove (0:Fin 1) = 0 := by decide
private theorem skip_3_0_0 : (0:Fin 3).succAbove (0:Fin 2) = 1 := by decide
private theorem skip_3_0_1 : (0:Fin 3).succAbove (1:Fin 2) = 2 := by decide
private theorem skip_3_1_0 : (1:Fin 3).succAbove (0:Fin 2) = 0 := by decide
private theorem skip_3_1_1 : (1:Fin 3).succAbove (1:Fin 2) = 2 := by decide
private theorem skip_3_2_0 : (2:Fin 3).succAbove (0:Fin 2) = 0 := by decide
private theorem skip_3_2_1 : (2:Fin 3).succAbove (1:Fin 2) = 1 := by decide
private theorem skip_4_0_0 : (0:Fin 4).succAbove (0:Fin 3) = 1 := by decide
private theorem skip_4_0_1 : (0:Fin 4).succAbove (1:Fin 3) = 2 := by decide
private theorem skip_4_0_2 : (0:Fin 4).succAbove (2:Fin 3) = 3 := by decide
private theorem skip_4_1_0 : (1:Fin 4).succAbove (0:Fin 3) = 0 := by decide
private theorem skip_4_1_1 : (1:Fin 4).succAbove (1:Fin 3) = 2 := by decide
private theorem skip_4_1_2 : (1:Fin 4).succAbove (2:Fin 3) = 3 := by decide
private theorem skip_4_2_0 : (2:Fin 4).succAbove (0:Fin 3) = 0 := by decide
private theorem skip_4_2_1 : (2:Fin 4).succAbove (1:Fin 3) = 1 := by decide
private theorem skip_4_2_2 : (2:Fin 4).succAbove (2:Fin 3) = 3 := by decide
private theorem skip_4_3_0 : (3:Fin 4).succAbove (0:Fin 3) = 0 := by decide
private theorem skip_4_3_1 : (3:Fin 4).succAbove (1:Fin 3) = 1 := by decide
private theorem skip_4_3_2 : (3:Fin 4).succAbove (2:Fin 3) = 2 := by decide
private theorem skip_5_0_0 : (0:Fin 5).succAbove (0:Fin 4) = 1 := by decide
private theorem skip_5_0_1 : (0:Fin 5).succAbove (1:Fin 4) = 2 := by decide
private theorem skip_5_0_2 : (0:Fin 5).succAbove (2:Fin 4) = 3 := by decide
private theorem skip_5_0_3 : (0:Fin 5).succAbove (3:Fin 4) = 4 := by decide
private theorem skip_5_1_0 : (1:Fin 5).succAbove (0:Fin 4) = 0 := by decide
private theorem skip_5_1_1 : (1:Fin 5).succAbove (1:Fin 4) = 2 := by decide
private theorem skip_5_1_2 : (1:Fin 5).succAbove (2:Fin 4) = 3 := by decide
private theorem skip_5_1_3 : (1:Fin 5).succAbove (3:Fin 4) = 4 := by decide
private theorem skip_5_2_0 : (2:Fin 5).succAbove (0:Fin 4) = 0 := by decide
private theorem skip_5_2_1 : (2:Fin 5).succAbove (1:Fin 4) = 1 := by decide
private theorem skip_5_2_2 : (2:Fin 5).succAbove (2:Fin 4) = 3 := by decide
private theorem skip_5_2_3 : (2:Fin 5).succAbove (3:Fin 4) = 4 := by decide
private theorem skip_5_3_0 : (3:Fin 5).succAbove (0:Fin 4) = 0 := by decide
private theorem skip_5_3_1 : (3:Fin 5).succAbove (1:Fin 4) = 1 := by decide
private theorem skip_5_3_2 : (3:Fin 5).succAbove (2:Fin 4) = 2 := by decide
private theorem skip_5_3_3 : (3:Fin 5).succAbove (3:Fin 4) = 4 := by decide
private theorem skip_5_4_0 : (4:Fin 5).succAbove (0:Fin 4) = 0 := by decide
private theorem skip_5_4_1 : (4:Fin 5).succAbove (1:Fin 4) = 1 := by decide
private theorem skip_5_4_2 : (4:Fin 5).succAbove (2:Fin 4) = 2 := by decide
private theorem skip_5_4_3 : (4:Fin 5).succAbove (3:Fin 4) = 3 := by decide

attribute [local simp] skip_2_0_0 skip_2_1_0 skip_3_0_0 skip_3_0_1 skip_3_1_0 skip_3_1_1 skip_3_2_0 skip_3_2_1 skip_4_0_0 skip_4_0_1 skip_4_0_2 skip_4_1_0 skip_4_1_1 skip_4_1_2 skip_4_2_0 skip_4_2_1 skip_4_2_2 skip_4_3_0 skip_4_3_1 skip_4_3_2 skip_5_0_0 skip_5_0_1 skip_5_0_2 skip_5_0_3 skip_5_1_0 skip_5_1_1 skip_5_1_2 skip_5_1_3 skip_5_2_0 skip_5_2_1 skip_5_2_2 skip_5_2_3 skip_5_3_0 skip_5_3_1 skip_5_3_2 skip_5_3_3 skip_5_4_0 skip_5_4_1 skip_5_4_2 skip_5_4_3

theorem hGram_det (t r s : K) :
    (hGram t r s).det =
      (1-t)*(1-r)*((1+t)*(1+r-2*t^2)-4*t^2+8*t^2*s-2*(1+r)*s^2) := by
  simp [hGram, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  ring

theorem hGram_envelope (t r s : K) (tp : 0<1+t) (rp : 0<1+r) :
    (hGram t r s).det =
      subK4Det t r - (1-t)*(1-r)*(2*(1+r))*(s-2*t^2/(1+r))^2 := by
  rw [hGram_det]
  unfold subK4Det pageFactor
  field_simp [ne_of_gt tp,ne_of_gt rp]
  <;> ring

theorem hGram_lt_book {t r s : K} (t0 : 0<t) (tHalf : t≤1/2)
    (rlo : -1<r) (rhi : r≤1) (p0 : 0≤pageFactor t r) :
    (hGram t r s).det<bThreeDet t := by
  have tp : 0<1+t := by linarith
  have rp : 0<1+r := by linarith
  rw [hGram_envelope t r s tp rp]
  have b : 0≤(1-t)*(1-r)*(2*(1+r))*(s-2*t^2/(1+r))^2 := by
    have a : 0≤1-t := by linarith
    have r' : 0≤1-r := by linarith
    positivity
  exact (sub_le_self _ b).trans_lt (subK4_gap t0 tHalf rlo p0)

#print axioms hGram_det
#print axioms hGram_lt_book
end RobustFolkman.GeometricGap
