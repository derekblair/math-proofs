import GeometricLinkCuts

namespace RobustFolkman.GeometricGap
open Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def cutSign (b : V→Bool) (v : V) : ℝ := if b v then 1 else -1
noncomputable def edgeFlip (b : V→Bool) (i j : V) : ℝ := if b i=b j then 0 else 1

theorem cutSign_product (b : V→Bool) (i j : V) :
    cutSign b i*cutSign b j=1-2*edgeFlip b i j := by
  cases hi : b i <;> cases hj : b j <;> norm_num [cutSign,edgeFlip,hi,hj]

theorem weighted_cut_quadratic (W : Matrix V V ℝ) (b : V→Bool) :
    cutSign b ⬝ᵥ (W *ᵥ cutSign b) =
      (∑ i, ∑ j, W i j)-2*(∑ i, ∑ j, W i j*edgeFlip b i j) := by
  simp only [dotProduct,Matrix.mulVec, Finset.mul_sum]
  have e (i j : V) :
      cutSign b i*(W i j*cutSign b j) = W i j - 2*(W i j*edgeFlip b i j) := by
    rw [show cutSign b i*(W i j*cutSign b j)=W i j*(cutSign b i*cutSign b j) by ring,
      cutSign_product]
    ring
  simp_rw [e, Finset.sum_sub_distrib]

theorem weighted_cut_bound (W : Matrix V V ℝ) (b : V→Bool) (ρ : ℝ)
    (h : -ρ*(∑ i, ∑ j, W i j) ≤ cutSign b ⬝ᵥ (W*ᵥcutSign b)) :
    (∑ i, ∑ j, W i j*edgeFlip b i j)≤((1+ρ)/2)*(∑ i, ∑ j, W i j) := by
  rw [weighted_cut_quadratic] at h
  nlinarith only [h]

#print axioms weighted_cut_bound
end RobustFolkman.GeometricGap
