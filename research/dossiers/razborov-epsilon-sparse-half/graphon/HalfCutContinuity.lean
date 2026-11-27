import CutEnergy

open MeasureTheory Set
open scoped ENNReal

namespace SparseHalfGraphon
variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

structure Half where
  f : X→ℝ
  measurable_f : Measurable f
  nn : ∀ x, 0≤f x
  le_one : ∀ x, f x≤1
  mass_half : (∫ x, f x ∂μ)=1/2

noncomputable def halfEnergy (K : Kernel X) (H : Half μ) : ℝ :=
  (∫ y, (∫ x, K.W (x,y)*H.f x ∂μ)*H.f y ∂μ)/2

noncomputable def beta (K : Kernel X) : ℝ :=
  sInf (Set.range (halfEnergy μ K))

noncomputable def constantHalf (h : mass μ=1) : Half μ where
  f := fun _ => (1/2:ℝ)
  measurable_f := measurable_const
  nn := fun _ => by norm_num
  le_one := fun _ => by norm_num
  mass_half := by
    rw [integral_const,smul_eq_mul]
    change mass μ * (1/2) = 1/2
    rw [h,one_mul]

lemma innerIntegrable (K : Kernel X) (H : Half μ) (y : X) :
    Integrable (fun x => K.W (x,y)*H.f x) μ := by
  have hm : Measurable (fun x => K.W (x,y)*H.f x) :=
    (K.measurable_W.comp (measurable_id.prodMk measurable_const)).mul H.measurable_f
  exact integrable_bounded μ hm
    (fun x => mul_nonneg (K.nonneg _) (H.nn _))
    (fun x => (mul_le_mul_of_nonneg_right (K.le_one _) (H.nn _)).trans
      (by simpa using H.le_one x))

lemma outerIntegrable (K : Kernel X) (H : Half μ) :
    Integrable (fun y => (∫ x, K.W (x,y)*H.f x ∂μ)*H.f y) μ := by
  have hm : Measurable (fun z : X×X => K.W z*H.f z.1) :=
    K.measurable_W.mul (H.measurable_f.comp measurable_fst)
  apply integrable_bounded μ (hm.stronglyMeasurable.integral_prod_left'.measurable.mul H.measurable_f)
    (fun y => mul_nonneg (integral_nonneg (fun x => mul_nonneg (K.nonneg _) (H.nn _))) (H.nn _))
    (C:=mass μ)
  intro y
  let c := ∫ x, K.W (x,y)*H.f x ∂μ
  have h0 : 0≤c := integral_nonneg (fun x => mul_nonneg (K.nonneg _) (H.nn _))
  have h1 : c≤mass μ := by
    have h := integral_mono (innerIntegrable μ K H y) (integrable_const (μ := μ) (1:ℝ))
      (fun x => (mul_le_mul_of_nonneg_right (K.le_one _) (H.nn _)).trans
        (by simpa using H.le_one x))
    simpa [c,mass,smul_eq_mul] using h
  exact (mul_le_mul_of_nonneg_left (H.le_one y) h0).trans (by simpa using h1)

theorem cut_half_cost (K J : Kernel X) (ε : ℝ) (hcut : CutBound μ K J ε)
    (H : Half μ) : |halfEnergy μ K H-halfEnergy μ J H|≤ε/2 := by
  have h := cut_product_test μ K J ε hcut H.f H.f H.measurable_f H.measurable_f
    H.nn H.le_one H.nn H.le_one
  have he : (∫ y, (∫ x, gapW K J (x,y)*H.f x ∂μ)*H.f y ∂μ) =
      (∫ y, (∫ x, K.W (x,y)*H.f x ∂μ)*H.f y ∂μ) -
        ∫ y, (∫ x, J.W (x,y)*H.f x ∂μ)*H.f y ∂μ := by
    have hrow (y : X) : (∫ x, gapW K J (x,y)*H.f x ∂μ) =
        (∫ x, K.W (x,y)*H.f x ∂μ) - ∫ x, J.W (x,y)*H.f x ∂μ := by
      simpa only [gapW,sub_mul] using
        (integral_sub (innerIntegrable μ K H y) (innerIntegrable μ J H y))
    simpa only [hrow,sub_mul] using
      (integral_sub (outerIntegrable μ K H) (outerIntegrable μ J H))
  rw [he] at h
  unfold halfEnergy
  rw [← sub_div,abs_div,abs_of_nonneg (by norm_num : 0≤(2:ℝ))]
  linarith [div_le_div_of_nonneg_right h (by norm_num : 0≤(2:ℝ))]

omit [IsFiniteMeasure μ] in
lemma range_bdd (K : Kernel X) : BddBelow (Set.range (halfEnergy μ K)) := by
  refine ⟨0, ?_⟩
  intro z hz
  rcases hz with ⟨H,rfl⟩
  unfold halfEnergy
  exact div_nonneg (integral_nonneg (fun y =>
    mul_nonneg (integral_nonneg (fun x => mul_nonneg (K.nonneg _) (H.nn _))) (H.nn _)))
    (by norm_num)

/-- On a probability space the optimum fractional half energy is
1/2-Lipschitz for the cut norm. -/
theorem cut_beta (hμ : mass μ=1) (K J : Kernel X) (ε : ℝ)
    (hcut : CutBound μ K J ε) : |beta μ K-beta μ J|≤ε/2 := by
  let H₀ := constantHalf μ hμ
  have hk0 : (Set.range (halfEnergy μ K)).Nonempty := ⟨_,⟨H₀,rfl⟩⟩
  have hj0 : (Set.range (halfEnergy μ J)).Nonempty := ⟨_,⟨H₀,rfl⟩⟩
  have hk1 (H : Half μ) : beta μ K≤halfEnergy μ K H :=
    csInf_le (range_bdd μ K) ⟨H,rfl⟩
  have hj1 (H : Half μ) : beta μ J≤halfEnergy μ J H :=
    csInf_le (range_bdd μ J) ⟨H,rfl⟩
  rw [abs_le]
  constructor
  · have hb : beta μ J-ε/2≤beta μ K := by
      apply le_csInf hk0
      rintro _ ⟨H,rfl⟩
      have ht := (abs_le.mp (cut_half_cost μ K J ε hcut H)).1
      linarith [hj1 H]
    linarith
  · have hb : beta μ K-ε/2≤beta μ J := by
      apply le_csInf hj0
      rintro _ ⟨H,rfl⟩
      have ht := (abs_le.mp (cut_half_cost μ K J ε hcut H)).2
      linarith [hk1 H]
    linarith

#print axioms cut_half_cost
#print axioms cut_beta
end SparseHalfGraphon
