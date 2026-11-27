import HalfCutContinuity
import IndependentRowsAE

open MeasureTheory Set
open scoped ENNReal

namespace SparseHalfGraphon
variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

def mixed (K L M : Kernel X) (z : (X×X)×X) : ℝ :=
  K.W z.1 * L.W (z.1.1,z.2) * M.W (z.1.2,z.2)

noncomputable def t3 (K L M : Kernel X) : ℝ :=
  ∫ z, mixed K L M z ∂(μ.prod μ).prod μ

lemma mixed_meas (K L M : Kernel X) : Measurable (mixed K L M) :=
  ((K.measurable_W.comp measurable_fst).mul
    (L.measurable_W.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))).mul
    (M.measurable_W.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

lemma mixed_nn (K L M : Kernel X) (z : (X×X)×X) : 0≤mixed K L M z :=
  mul_nonneg (mul_nonneg (K.nonneg _) (L.nonneg _)) (M.nonneg _)

lemma mixed_le (K L M : Kernel X) (z : (X×X)×X) : mixed K L M z≤1 := by
  unfold mixed
  have h := mul_le_mul_of_nonneg_right (K.le_one z.1) (L.nonneg (z.1.1,z.2))
  have h₁ : K.W z.1 * L.W (z.1.1,z.2)≤1 :=
    h.trans (by simpa using L.le_one (z.1.1,z.2))
  exact (mul_le_mul_of_nonneg_right h₁ (M.nonneg _)).trans (by simpa using M.le_one (z.1.2,z.2))

lemma mixed_int (K L M : Kernel X) : Integrable (mixed K L M) ((μ.prod μ).prod μ) :=
  integrable_bounded _ (mixed_meas K L M) (mixed_nn K L M) (mixed_le K L M)

lemma t3_cut_left (K J L M : Kernel X) (ε : ℝ) (hcut : CutBound μ K J ε) :
    |t3 μ K L M-t3 μ J L M|≤mass μ*ε := by
  let F : (X×X)×X→ℝ := fun z => mixed K L M z-mixed J L M z
  have iF : Integrable F ((μ.prod μ).prod μ) := (mixed_int μ K L M).sub (mixed_int μ J L M)
  have ht (v : X) : |∫ z, F (z,v) ∂μ.prod μ|≤ε := by
    let f : X→ℝ := fun x => L.W (x,v)
    let g : X→ℝ := fun y => M.W (y,v)
    let G : X×X→ℝ := fun z => gapW K J z*f z.1*g z.2
    have hm₁ : Measurable f := L.measurable_W.comp (measurable_id.prodMk measurable_const)
    have hm₂ : Measurable g := M.measurable_W.comp (measurable_id.prodMk measurable_const)
    have hmG : Measurable G :=
      ((K.measurable_W.sub J.measurable_W).mul (hm₁.comp measurable_fst)).mul
        (hm₂.comp measurable_snd)
    have hiG : Integrable G (μ.prod μ) := by
      apply Integrable.of_bound hmG.aestronglyMeasurable 1
      apply ae_of_all
      intro z
      simp only [G,Real.norm_eq_abs,abs_mul,abs_of_nonneg (show 0≤f z.1 from L.nonneg (z.1,v)),
        abs_of_nonneg (show 0≤g z.2 from M.nonneg (z.2,v))]
      have hh := mul_le_mul_of_nonneg_right (gapW_bound K J z) (L.nonneg (z.1,v))
      have hh₁ : |gapW K J z| *f z.1≤1 :=
        hh.trans (by simpa [f] using L.le_one (z.1,v))
      exact (mul_le_mul_of_nonneg_right hh₁ (M.nonneg _)).trans (by simpa [g] using M.le_one (z.2,v))
    have he : (fun z : X×X => F (z,v)) = G := by
      funext z
      simp only [F,G,mixed,gapW,f,g]
      ring
    rw [he,integral_prod_symm G hiG]
    have hrow (y : X) : (∫ x, G (x,y) ∂μ)=(∫ x, gapW K J (x,y)*f x ∂μ)*g y := by
      exact integral_mul_const (g y) (fun x => gapW K J (x,y)*f x)
    simp only [hrow]
    exact cut_product_test μ K J ε hcut f g hm₁ hm₂ (fun x => L.nonneg _)
      (fun x => L.le_one _) (fun y => M.nonneg _) (fun y => M.le_one _)
  have he : t3 μ K L M-t3 μ J L M = ∫ v, ∫ z, F (z,v) ∂μ.prod μ ∂μ := by
    unfold t3
    rw [← integral_sub (mixed_int μ K L M) (mixed_int μ J L M)]
    exact integral_prod_symm F iF
  rw [he]
  calc
    _ ≤ ∫ v, |∫ z, F (z,v) ∂μ.prod μ| ∂μ := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ:=μ) (f:=fun v => ∫ z, F (z,v) ∂μ.prod μ)
    _ ≤ mass μ*ε := by
      have hh := integral_mono iF.integral_prod_right.abs (integrable_const (μ:=μ) ε) ht
      simpa only [integral_const,mass,smul_eq_mul] using hh

lemma t3_swap12 (K L M : Kernel X) : t3 μ K L M=t3 μ K M L := by
  let e : (X×X)×X ≃ᵐ (X×X)×X :=
    (MeasurableEquiv.prodComm : X×X ≃ᵐ X×X).prodCongr (MeasurableEquiv.refl X)
  have hp : MeasurePreserving e ((μ.prod μ).prod μ) ((μ.prod μ).prod μ) :=
    (Measure.measurePreserving_swap (μ:=μ) (ν:=μ)).prod (MeasurePreserving.id μ)
  symm
  have h := hp.integral_comp' (mixed K L M)
  unfold t3
  rw [← h]
  apply integral_congr_ae
  apply ae_of_all
  rintro ⟨⟨x,y⟩,z⟩
  change K.W (x,y)*M.W (x,z)*L.W (y,z) = K.W (y,x)*L.W (y,z)*M.W (x,z)
  rw [K.symm x y]
  ring

lemma t3_swap23 (K L M : Kernel X) : t3 μ K L M=t3 μ L K M := by
  let a : (X×X)×X ≃ᵐ X×(X×X) := MeasurableEquiv.prodAssoc
  let b : X×(X×X) ≃ᵐ X×(X×X) :=
    (MeasurableEquiv.refl X).prodCongr (MeasurableEquiv.prodComm : X×X ≃ᵐ X×X)
  let e := a.trans (b.trans a.symm)
  have ha : MeasurePreserving a ((μ.prod μ).prod μ) (μ.prod (μ.prod μ)) :=
    measurePreserving_prodAssoc μ μ μ
  have hb : MeasurePreserving b (μ.prod (μ.prod μ)) (μ.prod (μ.prod μ)) :=
    (MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ:=μ) (ν:=μ))
  have hp : MeasurePreserving e ((μ.prod μ).prod μ) ((μ.prod μ).prod μ) :=
    ha.symm.comp (hb.comp ha)
  symm
  have h := hp.integral_comp' (mixed K L M)
  unfold t3
  rw [← h]
  apply integral_congr_ae
  apply ae_of_all
  rintro ⟨⟨x,y⟩,z⟩
  change L.W (x,y)*K.W (x,z)*M.W (y,z) = K.W (x,z)*L.W (x,y)*M.W (z,y)
  rw [M.symm y z]
  ring

/-- Cut counting lemma for triangles with constant three, rather than
a signed-coefficient constant. Also valid on finite subprobability spaces. -/
theorem t3_cut (K J : Kernel X) (ε : ℝ) (hcut : CutBound μ K J ε) :
    |t3 μ K K K-t3 μ J J J|≤3*mass μ*ε := by
  have h₁ := t3_cut_left μ K J K K ε hcut
  have h₂ : |t3 μ J K K-t3 μ J J K|≤mass μ*ε := by
    rw [t3_swap23 μ J K K]
    exact t3_cut_left μ K J J K ε hcut
  have h₃ : |t3 μ J J K-t3 μ J J J|≤mass μ*ε := by
    rw [t3_swap12 μ J J K,t3_swap23 μ J K J]
    exact t3_cut_left μ K J J J ε hcut
  rw [abs_le] at h₁ h₂ h₃ ⊢
  constructor <;> linarith

#print axioms t3_cut
end SparseHalfGraphon
