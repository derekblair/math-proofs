import BlockEnergyIncrement
import GraphonCaseTwo
open MeasureTheory Set
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

def pairLabel (c : X→ι) (z : X×X) := (c z.1,c z.2)

lemma pair_label_meas (c : X→ι) (hc : Measurable c) : Measurable (pairLabel c) :=
  hc.prodMap hc

lemma pair_cell (c : X→ι) (i j : ι) :
    cell (pairLabel c) (i,j)=cell c i ×ˢ cell c j := by
  ext z
  simp [cell,pairLabel,Prod.ext_iff]

lemma mean_cell_unit {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (W : Y→ℝ) (hW : Measurable W) (h₀ : ∀ z, 0≤W z) (h₁ : ∀ z, W z≤1)
    (c : Y→ι) (i : ι) : 0≤meanCell ν c W i ∧ meanCell ν c W i≤1 := by
  constructor
  · exact div_nonneg (integral_nonneg h₀) measureReal_nonneg
  · by_cases hz : ν.real (cell c i)=0
    · simp [meanCell,hz]
    · have hp : 0<ν.real (cell c i) := lt_of_le_of_ne measureReal_nonneg (Ne.symm hz)
      have hI := (integrable_bounded ν hW h₀ h₁).integrableOn (s:=cell c i)
      have hh := integral_mono hI (integrable_const (μ:=ν.restrict (cell c i)) (1:ℝ)) h₁
      apply (div_le_iff₀ hp).mpr
      simpa [setIntegral_const,smul_eq_mul] using hh

lemma mean_pair_symm (K : Kernel X) (c : X→ι) (i j : ι) :
    meanCell (μ.prod μ) (pairLabel c) K.W (i,j)=
    meanCell (μ.prod μ) (pairLabel c) K.W (j,i) := by
  unfold meanCell
  rw [pair_cell,pair_cell]
  have hi := setIntegral_prod_swap (μ:=μ) (ν:=μ) K.W (s:=cell c i) (t:=cell c j)
  have he : (fun z : X×X => K.W z.swap)=K.W := by
    funext z
    rcases z with ⟨x,y⟩
    exact K.symm y x
  rw [he] at hi
  rw [hi,measureReal_prod_prod,measureReal_prod_prod,mul_comm]

noncomputable def blockKernel (K : Kernel X) (c : X→ι) (hc : Measurable c) :
    Kernel X where
  W := meanBlock (μ.prod μ) (pairLabel c) K.W
  measurable_W := (block_bmeas (μ.prod μ) _ (pair_label_meas c hc) K.W).1
  nonneg := fun z => (mean_cell_unit (μ.prod μ) K.W K.measurable_W K.nonneg K.le_one _ _).1
  le_one := fun z => (mean_cell_unit (μ.prod μ) K.W K.measurable_W K.nonneg K.le_one _ _).2
  symm := fun x y => mean_pair_symm μ K c (c x) (c y)

noncomputable def blockEnergy (K : Kernel X) : ℝ := ∫ z, (K.W z)^2 ∂μ.prod μ

lemma block_energy_range (K : Kernel X) (hμ : mass μ=1) :
    0≤blockEnergy μ K ∧ blockEnergy μ K≤1 := by
  constructor
  · exact integral_nonneg (fun _ => sq_nonneg _)
  · have h₂ : ∀ z, (K.W z)^2≤1 := fun z => by
      simpa using pow_le_pow_left₀ (K.nonneg z) (K.le_one z) 2
    have hh := integral_mono
      (integrable_bounded (μ.prod μ) (K.measurable_W.pow_const 2) (fun _ => sq_nonneg _) h₂)
      (integrable_const (μ:=μ.prod μ) (1:ℝ)) h₂
    unfold blockEnergy
    rw [integral_const,smul_eq_mul,mul_one,← Set.univ_prod_univ,
      measureReal_prod_prod] at hh
    change _≤mass μ*mass μ at hh
    rwa [hμ,mul_one] at hh

#print axioms blockKernel
#print axioms block_energy_range
end SparseHalfGraphon
