import EditRoundMoments
open scoped BigOperators
namespace SparseHalfEditRound
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

noncomputable def integralLoss (F : V → V → I → I → ℝ) (q : V → I) : ℝ :=
  ∑ v, ∑ w, if v=w then 0 else F v w (q v) (q w)

noncomputable def fractionalLoss (r : V → I → ℝ) (F : V → V → I → I → ℝ) : ℝ :=
  ∑ v, ∑ w, ∑ i, ∑ j, r v i*r w j*F v w i j

theorem integralLoss_nonneg (F : V → V → I → I → ℝ) (hf : ∀ v w i j, 0 ≤ F v w i j)
    (q : V → I) : 0 ≤ integralLoss F q := by
  unfold integralLoss
  exact Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun w _ => by split <;> simp [hf]

theorem loss_bound (r : V → I → ℝ) (hr : ∀ v i, 0 ≤ r v i)
    (hs : ∀ v, ∑ i,r v i=1) (F : V → V → I → I → ℝ) (hf : ∀ v w i j, 0 ≤ F v w i j) :
    expectation r (integralLoss F) ≤ fractionalLoss r F := by
  unfold integralLoss fractionalLoss
  simp_rw [ex_sum]
  apply Finset.sum_le_sum
  intro v _
  apply Finset.sum_le_sum
  intro w _
  by_cases h : v=w
  · simp only [h,ite_true,expectation,mul_zero,Finset.sum_const_zero]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hr _ _) (hr _ _)) (hf _ _ _ _)
  · simp only [ite_eq_right h,ex_two_table r hs v w h, le_rfl]

noncomputable def boolLoss (G : V → V → Bool) (B : I → I → Bool) :
    V → V → I → I → ℝ :=
  fun v w i j => if G v w = B i j then 0 else 1

theorem boolLoss_nonneg (G : V → V → Bool) (B : I → I → Bool) :
    ∀ v w i j, 0 ≤ boolLoss G B v w i j := by
  intro v w i j
  unfold boolLoss
  split <;> norm_num

theorem directed_count (G : V → V → Bool) (B : I → I → Bool) (q : V → I)
    (gl : ∀ v, G v v = false) (bl : ∀ i, B i i = false) :
    integralLoss (boolLoss G B) q =
      ((Finset.univ.filter (fun z : V × V => G z.1 z.2 ≠ B (q z.1) (q z.2))).card : ℝ) := by
  let f (z : V × V) : ℝ := if G z.1 z.2 ≠ B (q z.1) (q z.2) then 1 else 0
  have hsum : (∑ z : V × V, f z) = ∑ v, ∑ w, f (v,w) := by
    rw [← Finset.univ_product_univ,Finset.sum_product]
  have hc : ((Finset.univ.filter (fun z : V × V => G z.1 z.2 ≠ B (q z.1) (q z.2))).card : ℝ) =
      ∑ z : V × V, f z := by
    simp only [f,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]
  rw [hc,hsum]
  unfold integralLoss
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : v=w
  · subst w
    simp [f,gl,bl]
  · simp [f,boolLoss,h]

#print axioms loss_bound
#print axioms directed_count
end SparseHalfEditRound
