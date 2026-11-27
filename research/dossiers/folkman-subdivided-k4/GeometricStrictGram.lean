import GeometricCompact

namespace RobustFolkman.GeometricGap
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def gramBlend (M A : Matrix I I ℝ) (z : ℝ) : Matrix I I ℝ :=
  (1-z) • M + z • A

theorem gramBlend_continuous (M A : Matrix I I ℝ) : Continuous (gramBlend M A) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun z : ℝ => (1-z)*M i j+z*A i j)
  exact ((continuous_const.sub continuous_id).mul continuous_const).add (continuous_id.mul continuous_const)

theorem gram_det_continuous : Continuous (fun M : Matrix I I ℝ => M.det) := by
  simp_rw [Matrix.det_apply']
  apply continuous_finsetSum _ fun p _ => Continuous.mul continuous_const ?_
  exact continuous_finsetProd _ fun i _ => (continuous_apply i).comp (continuous_apply (p i))

/-- Every strictly positive feasible determinant can be approximated by
positive definite feasible matrices strictly beyond all constrained edge
thresholds. No boundary determinant is lost in the lower Laplace bound. -/
theorem strictly_feasible_approx (C : I→I→Prop) (sym : ∀ i j, C i j ↔ C j i)
    (n : Fintype.card I≤6) (t : ℝ) (t0 : 0<t) (ts : t≤1/40000)
    (M : Matrix I I ℝ) (mf : GramFeasible C t M) (mp : 0<M.det)
    (mn : ∀ i j, |M i j-(1:Matrix I I ℝ) i j|≤27*t)
    (ε : ℝ) (ε0 : 0<ε) :
    ∃ Q : Matrix I I ℝ, Q.PosDef ∧ (∀ i, Q i i=1) ∧
      (∀ i j, C i j → t<Q i j) ∧ M.det-ε<Q.det ∧
      (∀ i j, |Q i j-(1:Matrix I I ℝ) i j|≤54*t) := by
  classical
  obtain ⟨A,af,ad⟩ := probe_exists C sym n (2*t) (by positivity) (by linarith only [ts])
  have dp : 0<A.det := by
    have q : (2*t)^2≤(1/20000:ℝ)^2 := (sq_le_sq₀ (by positivity) (by norm_num)).mpr
      (by linarith only [ts])
    nlinarith only [ad,q]
  have an (i j : I) : |A i j-(1:Matrix I I ℝ) i j|≤54*t := by
    have ll : 1-729*(2*t)^2≤A.det := by nlinarith only [ad,sq_nonneg t]
    have b := localized_offdiag A af.1 dp.ne' af.2.1 (2*t) (by positivity) ll i j
    exact b.trans_eq (by ring)
  let ε' := min ε (M.det/2)
  have ε'p : 0<ε' := lt_min ε0 (by positivity)
  have F : Continuous (fun z : ℝ => (gramBlend M A z).det) :=
    gram_det_continuous.comp (gramBlend_continuous M A)
  obtain ⟨δ,δ0,hδ⟩ := Metric.continuousAt_iff.mp F.continuousAt ε' ε'p
  let z := min (δ/2) (1/2)
  have z0 : 0<z := lt_min (by positivity) (by norm_num)
  have z1 : z≤1 := (min_le_right _ _).trans (by norm_num)
  have zδ : z<δ := (min_le_left _ _).trans_lt (by linarith only [δ0])
  let Q := gramBlend M A z
  have det : |Q.det-M.det|<ε' := by
    have dz : dist z (0:ℝ)<δ := by
      rw [Real.dist_eq,sub_zero,abs_of_pos z0]
      exact zδ
    have near := hδ dz
    simpa [Q,gramBlend, Real.dist_eq] using near
  have lo : M.det-ε'<Q.det := by
    have h := (abs_lt.mp det).1
    linarith only [h]
  have Qpos : 0<Q.det := by
    have e : ε'≤M.det/2 := min_le_right _ _
    linarith only [lo,e,mp]
  have ss : Q.PosSemidef := (mf.1.smul (sub_nonneg.mpr z1)).add (af.1.smul z0.le)
  refine ⟨Q,pd_of_psd_det Q ss Qpos.ne',?_,?_,?_,?_⟩
  · intro i
    change (1-z)*M i i+z*A i i=1
    rw [mf.2.1,af.2.1]
    ring
  · intro i j h
    change t<(1-z)*M i j+z*A i j
    have h1 := mul_le_mul_of_nonneg_left (mf.2.2 i j h) (sub_nonneg.mpr z1)
    have h2 := mul_le_mul_of_nonneg_left (af.2.2 i j h) z0.le
    have pos := mul_pos z0 t0
    nlinarith only [h1,h2,pos]
  · have ee : ε'≤ε := min_le_left _ _
    linarith only [lo,ee]
  · intro i j
    have eq : Q i j-(1:Matrix I I ℝ) i j =
        (1-z)*(M i j-(1:Matrix I I ℝ) i j)+z*(A i j-(1:Matrix I I ℝ) i j) := by
      change (1-z)*M i j+z*A i j-(1:Matrix I I ℝ) i j=_
      ring
    rw [eq]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr z1),abs_of_pos z0]
    have u := mul_le_mul_of_nonneg_left (mn i j) (sub_nonneg.mpr z1)
    have v := mul_le_mul_of_nonneg_left (an i j) z0.le
    have extra := mul_nonneg (sub_nonneg.mpr z1) t0.le
    nlinarith only [u,v,extra]

#print axioms strictly_feasible_approx
end RobustFolkman.GeometricGap
