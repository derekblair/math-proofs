import TableL1Limit
import CutExceptional
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Set Function Filter Topology
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

lemma Kernel.bmeas (K : Kernel X) : BMeas K.W :=
  ⟨K.measurable_W, 1, fun z => by rw [abs_of_nonneg (K.nonneg z)]; exact K.le_one z⟩

noncomputable def kernelL1 (K : Kernel X) : (X×X) →₁[μ.prod μ] ℝ :=
  (bMeas_integrable _ K.bmeas).toL1 K.W

/-- An L¹ limit of kernels has an everywhere bounded, pointwise symmetric
measurable representative, even on a non-complete base measure space. -/
theorem kernel_L1_closed (Ks : ℕ → Kernel X) (F : (X×X) →₁[μ.prod μ] ℝ)
    (hF : Tendsto (fun n => kernelL1 μ (Ks n)) atTop (𝓝 F)) :
    ∃ K : Kernel X, kernelL1 μ K = F := by
  have : Fact ((1 : ENNReal) ≤ 1) := ⟨le_rfl⟩
  obtain ⟨ns, hns, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hF).exists_seq_tendsto_ae
  have hn : ∀ᵐ z ∂μ.prod μ, ∀ n, kernelL1 μ (Ks n) z = (Ks n).W z :=
    ae_all_iff.mpr fun n => Integrable.coeFn_toL1 _
  have hlim' : ∀ᵐ z ∂μ.prod μ, Tendsto (fun n => (Ks (ns n)).W z) atTop (𝓝 (F z)) := by
    filter_upwards [hn, hlim] with z hz hl
    simpa only [hz] using hl
  have hs := Measure.measurePreserving_swap (μ:=μ) (ν:=μ)
  have hlimSwap := hs.quasiMeasurePreserving.ae hlim'
  have hsym : ∀ᵐ z ∂μ.prod μ, F z = F z.swap := by
    filter_upwards [hlim', hlimSwap] with z hz hz'
    change Tendsto (fun n => (Ks (ns n)).W z.swap) atTop (𝓝 (F z.swap)) at hz'
    rcases z with ⟨x,y⟩
    have eq : (fun n => (Ks (ns n)).W ((x,y).swap)) =
        (fun n => (Ks (ns n)).W (x,y)) :=
      funext (fun n => ((Ks (ns n)).symm x y).symm)
    rw [eq] at hz'
    exact tendsto_nhds_unique hz hz' 
  have hstrong := Lp.aestronglyMeasurable F
  let G : X×X → ℝ := fun z => max 0 (min 1 (hstrong.mk F z))
  have hm : Measurable G := measurable_const.max (measurable_const.min hstrong.measurable_mk)
  have h0 z : 0 ≤ G z := le_max_left _ _
  have h1 z : G z ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have hG : ∀ᵐ z ∂μ.prod μ, G z = F z := by
    filter_upwards [hstrong.ae_eq_mk,hlim'] with z hz hl
    have hv : F z ∈ Icc (0:ℝ) 1 := isClosed_Icc.mem_of_tendsto hl
      (Eventually.of_forall fun n => ⟨(Ks (ns n)).nonneg z, (Ks (ns n)).le_one z⟩)
    change max 0 (min 1 (hstrong.mk F z)) = F z
    rw [← hz, min_eq_right hv.2, max_eq_right hv.1]
  let K : Kernel X :=
    ⟨fun z => (G z + G z.swap) / 2,
      (hm.add (hm.comp measurable_swap)).div_const 2,
      fun z => by linarith [h0 z,h0 z.swap],
      fun z => by linarith [h1 z,h1 z.swap],
      fun x y => by change (G (x,y)+G (y,x))/2=(G (y,x)+G (x,y))/2; ring⟩
  have hKF : K.W =ᵐ[μ.prod μ] F := by
    filter_upwards [hG, hs.quasiMeasurePreserving.ae hG, hsym] with z hz hz' h
    change (G z + G z.swap) / 2 = F z
    change G z.swap = F z.swap at hz'
    rw [hz, hz', ← h]
    ring
  refine ⟨K, Lp.ext ?_⟩
  exact (Integrable.coeFn_toL1 _).trans hKF

/-- The representative obtained by L¹ completion is also approached in cut. -/
theorem kernel_L1_limit_cut (Ks : ℕ → Kernel X) (F : (X×X) →₁[μ.prod μ] ℝ)
    (hF : Tendsto (fun n => kernelL1 μ (Ks n)) atTop (𝓝 F)) :
    ∃ K : Kernel X, kernelL1 μ K = F ∧
      ∀ ε > 0, ∀ᶠ n in atTop, CutBound μ (Ks n) K ε := by
  obtain ⟨K,hK⟩ := kernel_L1_closed μ Ks F hF
  refine ⟨K,hK,?_⟩
  intro ε hε
  rw [← hK] at hF
  filter_upwards [Metric.tendsto_nhds.mp hF ε hε] with n hn
  apply L1_imp_cut
  exact ((dist_real_L1 _ (Ks n).W K.W _ _).symm.trans_lt hn).le

#print axioms kernel_L1_closed
#print axioms kernel_L1_limit_cut
end SparseHalfGraphon
