import StrictAnchorHalf
import TriangleAE

open Set MeasureTheory Function Filter
open scoped ENNReal
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

def rowSupport (W : Kernel X) (v : X) (S : Set X) : Set X :=
  S ∩ {x | 0 < W.W (v,x)}

lemma rowSupport_meas (W : Kernel X) (v : X) {S : Set X} (hS : MeasurableSet S) :
    MeasurableSet (rowSupport W v S) :=
  hS.inter (measurableSet_lt measurable_const (rowMeasurable W v))

/-- Proof of the strict root test used before the two saturation cases.
The fractional weighting is constant on the entire eligible support,
so no atomless subset exists lemma is needed. -/
theorem root_eligible_lt (W : Kernel X) (a : X→ℝ)
    (ha : Measurable a) (ha₀ : ∀ x, 0 ≤ a x) (ha₁ : ∀ x, a x ≤ 1)
    (haM : (∫ x,a x ∂μ)=2/5) (haI : energyPair μ W a a=0)
    (htri : ∀ᵐ z ∂(μ.prod μ).prod μ, triangle W z=0)
    (hb : 1/50 ≤ beta μ W)
    (S L : Set X) (hS : MeasurableSet S) (hL : MeasurableSet L) (hLS : L ⊆ S)
    (hsa : ∀ x∈S, a x=0)
    (hsd : ∀ x∈S, deg (reweight μ a) W x ≤ 1/5)
    (hld : ∀ x∈L, deg (reweight μ a) W x < 1/5) :
    ∀ᵐ v ∂μ, 0 < μ (rowSupport W v L) → μ.real (rowSupport W v S) < 1/10 := by
  have htm : MeasurableSet {z | triangle W z=0} :=
    measurableSet_eq_fun (triangle_measurable W) measurable_const
  have ht : ∀ᵐ v ∂μ, ∀ᵐ z ∂μ.prod μ, triangle W (z,v)=0 :=
    (Measure.ae_ae_comm htm).mp (Measure.ae_ae_of_ae_prod htri)
  have : IsFiniteMeasure (reweight μ a) := isFiniteMeasure_of_le μ (reweight_le μ a ha₁)
  filter_upwards [ht] with v hv hPL
  let B := rowSupport W v S
  let C := rowSupport W v L
  have hCB : C ⊆ B := fun _ hx => ⟨hLS hx.1,hx.2⟩
  have hB : MeasurableSet B := rowSupport_meas W v hS
  by_contra! hM
  change 1/10 ≤ μ.real B at hM
  have hp : 0 < μ.real B := by linarith
  let r : ℝ := (1/10)/μ.real B
  have r0 : 0 < r := div_pos (by norm_num) hp
  have r1 : r ≤ 1 := (div_le_iff₀ hp).mpr (by simpa using hM)
  let e : X→ℝ := B.indicator (fun _ => r)
  have hem : Measurable e := measurable_const.indicator hB
  have e0 (x) : 0≤e x := by
    classical
    by_cases hx : x∈B <;> simp [e,hx,r0.le]
  have e1 (x) : e x≤1 := by
    classical
    by_cases hx : x∈B <;> simp [e,hx,r1]
  have he := BMeas.of_unit hem e0 e1
  have hcap (x) : a x+e x≤1 := by
    classical
    by_cases hx : x∈B
    · simp [e,hx,hsa x hx.1,r1]
    · simpa [e,hx] using ha₁ x
  have hE : (∫ x,e x ∂μ)=1/10 := by
    unfold e
    rw [integral_indicator hB,setIntegral_const,smul_eq_mul]
    exact (mul_comm _ _).trans (div_mul_cancel₀ _ hp.ne')
  have hEE : energyPair μ W e e=0 := by
    unfold energyPair
    have hzero : (fun z:X×X => e z.1*e z.2*W.W z) =ᵐ[μ.prod μ] 0 := by
      filter_upwards [hv] with z hz
      by_cases hx : z.1∈B
      · by_cases hy : z.2∈B
        · have hz' : W.W z=0 := by
            unfold triangle at hz
            rw [W.symm z.1 v,W.symm z.2 v] at hz
            exact (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hy.2.ne')).resolve_right hx.2.ne'
          simp [hz']
        · simp [e,hy]
      · simp [e,hx]
    rw [integral_congr_ae hzero]
    exact integral_zero _ _
  have hZ : 0<defMass μ (reweight μ a) W e := by
    unfold defMass
    let g : X→ℝ := fun x => e x*deficit (reweight μ a) W x
    have gi : Integrable g μ := bMeas_integrable μ
      (he.mul ((BMeas.const _).sub (deg_bmeas (reweight μ a) W)))
    have g0 : 0≤g := by
      intro x
      by_cases hx : x∈B
      · exact mul_nonneg (e0 x) (sub_nonneg.mpr (hsd x hx.1))
      · simp [g,e,hx]
    have hcs : C ⊆ support g := by
      intro x hx
      apply ne_of_gt
      exact mul_pos (by simpa [e,hCB hx] using r0) (sub_pos.mpr (hld x hx.1))
    exact (integral_pos_iff_support_of_nonneg g0 gi).mpr (hPL.trans_le (measure_mono hcs))
  exact (not_lt_of_ge hb) (strict_anchor_deficit μ W a e ha he ha₀ e0 hcap haM hE haI hEE hZ)

#print axioms root_eligible_lt
end SparseHalfGraphon
