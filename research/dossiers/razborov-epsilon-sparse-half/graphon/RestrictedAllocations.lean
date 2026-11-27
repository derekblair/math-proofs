import OutsideHighIsolates
import SmallLowBalanced
import SmallLowFill

open Set MeasureTheory Function Filter
open scoped ENNReal
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

noncomputable def indicatorWeight (S : Set X) : X→ℝ := S.indicator (fun _=>1)

lemma indicatorWeight_reweight (S : Set X) (hS : MeasurableSet S) :
    reweight μ (indicatorWeight S)=μ.restrict S := by
  unfold reweight
  have he : (fun x => ENNReal.ofReal (indicatorWeight S x)) = S.indicator (fun _ => 1) := by
    classical
    funext x
    by_cases hx : x∈S <;> simp [indicatorWeight,hx]
  rw [he]
  exact withDensity_indicator_one hS

lemma restrict_real_sub (S T : Set X) (hT : MeasurableSet T) (hTS : T⊆S) :
    (μ.restrict S).real T=μ.real T := by
  simp only [Measure.real,Measure.restrict_apply hT,inter_eq_left.mpr hTS]

lemma mass_compl_add (S : Set X) (hS : MeasurableSet S) :
    μ.real Sᶜ + μ.real S=mass μ := by
  rw [compl_eq_univ_sdiff,measureReal_sdiff (subset_univ S) hS]
  unfold mass
  ring

lemma supported_integral_restrict (S : Set X) (hS : MeasurableSet S)
    (F : X→ℝ) (hF : ∀ x∉S, F x=0) :
    (∫ x, F x ∂μ.restrict S) = ∫ x, F x ∂μ := by
  rw [← integral_indicator hS]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  classical
  by_cases hx:x∈S <;> simp [hx,hF]

lemma supported_load_restrict (S : Set X) (hS : MeasurableSet S)
    (K : Kernel X) (D : X→ℝ) (hD : ∀ x∉S, D x=0) (v : X) :
    load (μ.restrict S) K D v=load μ K D v :=
  supported_integral_restrict μ S hS _ (fun x hx=>by simp [hD x hx])

lemma zero_rectangle_restrict_lift (S T : Set X) (hS : MeasurableSet S)
    (hT : MeasurableSet T) (hTS : T⊆S) (K : Kernel X)
    (h : ∀ᵐ z ∂(μ.restrict S).prod (μ.restrict S), z.1∈T → z.2∈T → K.W z=0) :
    ∀ᵐ z ∂μ.prod μ, z.1∈T → z.2∈T → K.W z=0 := by
  rw [Measure.prod_restrict] at h
  have h' : ∀ᵐ z ∂μ.prod μ, z∈S×ˢS → (z.1∈T → z.2∈T → K.W z=0) :=
    (ae_restrict_iff' (hS.prod hS)).mp h
  filter_upwards [h'] with z hz hz1 hz2
  exact hz ⟨hTS hz1,hTS hz2⟩ hz1 hz2

lemma degree_disjoint_cap (S T : Set X) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hD : Disjoint S T) (K : Kernel X) (x : X) :
    deg (μ.restrict T) K x ≤ deg μ K x - deg (μ.restrict S) K x := by
  have h := setIntegral_union hD hT (row_integrable μ K x).integrableOn
    (row_integrable μ K x).integrableOn
  have hi : (∫ y in S∪T,K.W (x,y) ∂μ)≤∫ y,K.W (x,y) ∂μ :=
    integral_mono_measure Measure.restrict_le_self (ae_of_all _ (fun _=>K.nonneg _))
      (row_integrable μ K x)
  change (∫ y in S∪T,K.W (x,y) ∂μ)=_ at h
  rw [h] at hi
  change deg (μ.restrict S) K x+deg (μ.restrict T) K x≤deg μ K x at hi
  linarith

#print axioms zero_rectangle_restrict_lift
#print axioms degree_disjoint_cap
end SparseHalfGraphon
