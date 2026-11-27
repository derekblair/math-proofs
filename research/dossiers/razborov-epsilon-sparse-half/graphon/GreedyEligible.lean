import GreedyBoundKernel
import RestrictedAllocations
import HighMarkFinite

open Set MeasureTheory Function Filter
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

lemma indicatorWeight_unit (S : Set X) (hS : MeasurableSet S) :
    Measurable (indicatorWeight S) ∧ ∀ x, 0 ≤ indicatorWeight S x ∧ indicatorWeight S x≤1 := by
  refine ⟨measurable_const.indicator hS,?_⟩
  intro x
  classical
  by_cases h:x∈S <;> simp [indicatorWeight,h]

lemma indicatorWeight_mass (S : Set X) (hS : MeasurableSet S) :
    (∫ x,indicatorWeight S x ∂μ)=μ.real S := by
  rw [indicatorWeight,integral_indicator hS,setIntegral_const,smul_eq_mul,mul_one]

lemma zero_supported_half (W : Kernel X) (B : Set X) (hmB : MeasurableSet B)
    (h : (1/2:ℝ)≤μ.real B)
    (hInd : ∀ᵐ z ∂μ.prod μ, z.1∈B → z.2∈B → W.W z=0) : beta μ W≤0 := by
  let f := allocSet μ B (1/2)
  let bf := allocSet_bmeas μ B hmB (1/2) (by norm_num) h
  let H : Half μ := ⟨f,bf.1,allocSet_nn μ B _ (by norm_num),allocSet_le μ B _ h,
    allocSet_mass μ B hmB _ (by norm_num) h⟩
  have he : halfEnergy μ W H = 0 := by
    rw [halfEnergy_as_pair]
    have hh : (fun z:X×X => f z.1*f z.2*W.W z) =ᵐ[μ.prod μ] 0 := by
      classical
      filter_upwards [hInd] with z hz
      by_cases h₁:z.1∈B
      · by_cases h₂:z.2∈B
        · simp [hz h₁ h₂]
        · simp [f,allocSet_support μ B _ h₂]
      · simp [f,allocSet_support μ B _ h₁]
    change (∫ z, f z.1*f z.2*W.W z ∂μ.prod μ)/2=0
    rw [integral_congr_ae hh]
    simp
  exact (csInf_le (range_bdd μ W) ⟨H,rfl⟩).trans_eq he

/-- The eligible tail in both Razborov cases can be chosen fractionally
at its exact mass. The finite high-side independence bound is an explicit input. -/
theorem greedy_from_high_cap (hμ : mass μ=1) (W : Kernel X) (B : Set X) (hmB : MeasurableSet B)
    (a : ℝ) (ha : 39/100≤a) (ha' : a<1/2)
    (hab : a≤μ.real B) (hb : μ.real B≤1/2)
    (hCost : energyPair μ W (indicatorWeight B) (indicatorWeight B)/2≤
      (1/2-a)*(μ.real B-a))
    (ht : ∀ z, triangle W z=0)
    (hFloor : ∀ x∉B, 1/2-a≤deg (μ.restrict B) W x)
    (hHigh : μ.real (highOutside μ W B (μ.real B/2))≤a) :
    beta μ W≤a*(1/2-a)/2-(3/100)*(μ.real B-a) := by
  let b := μ.real B
  let S := Bᶜ \ highOutside μ W B (b/2)
  let d : ℝ := 1-a-b
  have sm : MeasurableSet S := hmB.compl.diff
    (hmB.compl.inter (measurableSet_lt measurable_const (deg_measurable _ W)))
  have hS : d≤μ.real S := by
    have hh : highOutside μ W B (b/2) ⊆ Bᶜ := fun _ hx=>hx.1
    rw [show S = Bᶜ \ highOutside μ W B (b/2) from rfl,measureReal_sdiff hh
      (hmB.compl.inter (measurableSet_lt measurable_const (deg_measurable _ W)))]
    have ha := mass_compl_add μ B hmB
    dsimp [b,d] at *
    linarith
  have d0 : 0≤d := by dsimp [d,b]; linarith
  let D := allocSet μ S d
  have hD := allocSet_bmeas μ S sm d d0 hS
  have hB := indicatorWeight_unit B hmB
  have haD (x) : indicatorWeight B x+D x≤1 := by
    classical
    by_cases hx:x∈B
    · have hz : x∉S := fun h=>h.1 hx
      simp [indicatorWeight,hx,D,allocSet_support μ S d hz]
    · simpa [indicatorWeight,hx] using allocSet_le μ S d hS x
  have hd (x) (hx : 0<D x) :
      1/2-a≤deg (reweight μ (indicatorWeight B)) W x ∧
      deg (reweight μ (indicatorWeight B)) W x≤b/2 := by
    have hm : x∈S := by
      by_contra! h
      unfold D at hx
      rw [allocSet_support μ S d h] at hx
      exact (lt_irrefl _ hx)
    rw [indicatorWeight_reweight μ B hmB]
    exact ⟨hFloor x hm.1,le_of_not_gt (fun h=>hm.2 ⟨hm.1,h⟩)⟩
  exact greedy_bound_kernel μ W _ D hB.1 hD.1 (fun x=>(hB.2 x).1)
    (allocSet_nn μ S d d0) haD a b ha ha' hab hb (indicatorWeight_mass μ B hmB)
    (allocSet_mass μ S sm d d0 hS) hCost ht hd

#print axioms zero_supported_half
#print axioms greedy_from_high_cap
end SparseHalfGraphon
