import EditRoundProduct
open scoped BigOperators
namespace SparseHalfEditRound
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

noncomputable def indicator (i j : I) : ℝ := if i=j then 1 else 0

theorem ex_two_table (r : V → I → ℝ) (hs : ∀ v, ∑ i, r v i = 1)
    (v w : V) (hvw : v ≠ w) (F : I → I → ℝ) :
    expectation r (fun q => F (q v) (q w)) =
      ∑ i, ∑ j, r v i * r w j * F i j := by
  classical
  have table (q : V → I) : F (q v) (q w) =
      ∑ i, ∑ j, indicator i (q v) * (indicator j (q w)*F i j) := by
    simp [indicator,ite_mul,mul_ite]
  simp_rw [table,ex_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [ex_two r hs v w hvw (indicator i) (fun z => indicator j z * F i j)]
  simp [indicator,ite_mul,mul_ite,mul_assoc,eq_comm]

noncomputable def meanCount (r : V → I → ℝ) (i : I) : ℝ := ∑ v, r v i
noncomputable def actualCount (q : V → I) (i : I) : ℝ := ∑ v, indicator i (q v)

theorem count_is_fiber (q : V → I) (i : I) :
    actualCount q i = ((Finset.univ.filter (fun v => q v = i)).card : ℝ) := by
  unfold actualCount indicator
  simp only [eq_comm,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]

private theorem ex_const (r : V → I → ℝ) (hs : ∀ v, ∑ i, r v i = 1) (a : ℝ) :
    expectation r (fun _ => a) = a := by
  rw [expectation,← Finset.sum_mul,prob_total r hs,one_mul]

theorem variance_bound (r : V → I → ℝ) (hr : ∀ v i, 0 ≤ r v i)
    (hu : ∀ v i, r v i ≤ 1) (hs : ∀ v, ∑ i, r v i = 1)
    (i : I) :
    expectation r (fun q => (actualCount q i-meanCount r i)^2) ≤ Fintype.card V := by
  classical
  let x (v : V) (j : I) := indicator i j-r v i
  have zero (v : V) : (∑ j, r v j*x v j) = 0 := by
    simp only [x,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hs,one_mul,indicator,mul_ite,mul_one,mul_zero]
    simp [eq_comm]
  have sq (q : V → I) : (actualCount q i-meanCount r i)^2 =
      ∑ v, ∑ w, x v (q v)*x w (q w) := by
    unfold actualCount meanCount
    rw [← Finset.sum_sub_distrib, pow_two, Finset.sum_mul_sum]
  have bounds (v : V) (j : I) : (x v j)^2 ≤ 1 := by
    unfold x indicator
    split <;> nlinarith [hr v i,hu v i,mul_nonneg (hr v i) (sub_nonneg.mpr (hu v i))]
  have H (v w : V) :
      expectation r (fun q => x v (q v)*x w (q w)) ≤ if v=w then 1 else 0 := by
    by_cases h : v=w
    · subst w
      rw [ite_eq_left rfl, ← ex_const r hs 1]
      exact ex_mono r hr _ _ (fun q => by simpa only [pow_two] using bounds v (q v))
    · rw [ex_two r hs v w h,zero,zero,zero_mul,ite_eq_right h]
  simp_rw [sq,ex_sum]
  refine (Finset.sum_le_sum (fun v _ => Finset.sum_le_sum (fun w _ => H v w))).trans ?_
  simp [Finset.sum_ite_eq,Finset.sum_const]

#print axioms ex_two_table
#print axioms variance_bound
end SparseHalfEditRound
