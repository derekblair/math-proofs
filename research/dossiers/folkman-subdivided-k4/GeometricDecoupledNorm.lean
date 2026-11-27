import GeometricDecoupling
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Linarith

namespace RobustFolkman.GeometricGap
open Finset Matrix
variable {J : Type*} [Fintype J] [DecidableEq J]
variable {H : Type*} [SeminormedAddCommGroup H] [NormedSpace ℝ H]

/-- This applies in particular when T is the linear map taking a
matrix to its Euclidean operator. It does not use a concentration
bound or assume independent off-diagonal entries. -/
theorem norm_cross_part_average (T : Matrix J J ℝ →ₗ[ℝ] H)
    (A : Matrix J J ℝ) (diag : ∀ i, A i i=0) :
    ‖T A‖ ≤ (2/(Fintype.card (J→Bool):ℝ)) *
      ∑ b : J→Bool, ‖T (crossPart A b)‖ := by
  let C : ℝ := Fintype.card (J→Bool)
  letI : Nonempty (J→Bool) := ⟨fun _ => false⟩
  have C0 : 0<C := by dsimp [C]; exact_mod_cast Fintype.card_pos (α:=J→Bool)
  have h := congrArg T (sum_crossParts A diag)
  simp only [map_smul,map_sum] at h
  change (2:ℝ) • (∑ b, T (crossPart A b))=C • T A at h
  have hs := congrArg norm h
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ)≤2),
    abs_of_pos C0] at hs
  have A' := norm_sum_le (Finset.univ : Finset (J→Bool)) (fun b => T (crossPart A b))
  have hh := mul_le_mul_of_nonneg_left A' (by norm_num : (0:ℝ)≤2)
  rw [hs] at hh
  change ‖T A‖ ≤ (2/C) * _
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ C0).2 (by simpa only [mul_comm ‖T A‖ C] using hh)

#print axioms norm_cross_part_average
end RobustFolkman.GeometricGap
