import GeometricDirectedLinkSum
import GeometricCutTransfer

namespace RobustFolkman.GeometricGap
open Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem constant_matrix_quadratic (q : ℝ) (x : V→ℝ) :
    x ⬝ᵥ ((Matrix.of (fun _ _ : V => q)) *ᵥ x) = q*(∑ i, x i)^2 := by
  simp only [dotProduct,Matrix.mulVec,Matrix.of_apply, ←Finset.mul_sum, ←Finset.sum_mul]
  ring

/-- The usual unnormalized centered-matrix estimate suffices for
the 9/16 cut bound. The same hypothesis supplies the edge-count
lower bound, so no separate degree concentration is needed. -/
theorem cuts_from_centered_quadratic (F : EdgeGraph V) (q : ℝ) (q0 : 0≤q)
    (two : ∀ e∈F, (e:Finset V).card=2)
    (center : ∀ x : V → ℝ,
      -(Fintype.card V:ℝ)*q/10*(∑ i, (x i)^2) ≤
        x ⬝ᵥ ((linkAdjMatrix F - (Matrix.of (fun _ _ : V => q))) *ᵥ x)) :
    ∀ b : V → Bool, cutCount F b ≤ (9/16)*(F.card:ℝ) := by
  let n : ℝ := Fintype.card V
  let A := linkAdjMatrix F
  have cv (x : V→ℝ) :
      -n*q/10*(∑ i, (x i)^2)+q*(∑ i, x i)^2 ≤ x ⬝ᵥ (A *ᵥ x) := by
    have h := center x
    change _≤ x ⬝ᵥ ((A-(Matrix.of (fun _ _ : V => q))) *ᵥ x) at h
    rw [Matrix.sub_mulVec,dotProduct_sub,constant_matrix_quadratic] at h
    linarith only [h]
  have vol : 9/10*n^2*q ≤ ∑ i, ∑ j, A i j := by
    have h := cv (fun _ => (1:ℝ))
    simp only [one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
      dotProduct,Matrix.mulVec,one_mul] at h
    change -n*q/10*n+q*n^2≤_ at h
    nlinarith only [h]
  intro b
  have h := cv (cutSign b)
  have sig (i : V) : (cutSign b i)^2=1 := by unfold cutSign; split <;> norm_num
  simp only [sig,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at h
  change -n*q/10*n+q*(∑ i, cutSign b i)^2≤_ at h
  have z : 0≤q*(∑ i, cutSign b i)^2 := by positivity
  have np : 0≤n^2*q := by positivity
  have L : -(1/8:ℝ)*(∑ i,∑ j,A i j)≤cutSign b ⬝ᵥ (A *ᵥ cutSign b) :=
    by nlinarith only [h,vol,z,np]
  have K := weighted_cut_bound A b (1/8) L
  change (∑ i,∑ j,linkAdjMatrix F i j*edgeFlip b i j) ≤
    ((1+(1:ℝ)/8)/2)*(∑ i,∑ j,linkAdjMatrix F i j) at K
  rw [directed_cut_count F two b,directed_orient_count F two] at K
  unfold cutCount
  linarith only [K]

#print axioms cuts_from_centered_quadratic
end RobustFolkman.GeometricGap
