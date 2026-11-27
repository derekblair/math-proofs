import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

open scoped BigOperators

namespace BooleanRealAmplitudeRank

theorem real_minor_atom (a b c d : ℝ) :
    (a*d-c*b)^2 = a^2*d^2+b^2*c^2-2*(a*b)*(c*d) := by ring

theorem diagonal_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) {u v : ι} (h : u ≠ v) :
    (∏ i : ι, d i) = d u * d v * ∏ i ∈ (Finset.univ.erase u).erase v, d i := by
  have hu : u ∈ (Finset.univ : Finset ι) := Finset.mem_univ _
  have hv : v ∈ (Finset.univ : Finset ι).erase u :=
    Finset.mem_erase.mpr ⟨Ne.symm h, Finset.mem_univ _⟩
  calc
    (∏ i, d i) = d u * ∏ i ∈ Finset.univ.erase u, d i :=
      (Finset.mul_prod_erase _ _ hu).symm
    _ = d u * (d v * ∏ i ∈ (Finset.univ.erase u).erase v, d i) := by
      rw [Finset.mul_prod_erase _ _ hv]
    _ = _ := by ring

theorem separable_filler {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b d : ι → ℝ) {u v : ι} (huv : u ≠ v)
    (hu : d u ≠ 0) (hv : d v ≠ 0) :
    a u * b v * (∏ i ∈ (Finset.univ.erase u).erase v, d i) =
    (∏ i : ι, d i) * (a u / d u) * (b v / d v) := by
  rw [diagonal_product d huv]
  field_simp

theorem block_nine_constant :
    (4 * (9-1) : ℚ) / (3*9) = 32/27 := by norm_num

end BooleanRealAmplitudeRank

#print axioms BooleanRealAmplitudeRank.real_minor_atom
#print axioms BooleanRealAmplitudeRank.diagonal_product
#print axioms BooleanRealAmplitudeRank.separable_filler
#print axioms BooleanRealAmplitudeRank.block_nine_constant
