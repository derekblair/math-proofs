import GraphonCaseTwoLocal

open MeasureTheory Set
namespace SparseHalfGraphon

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def pullKernel (K : Kernel Y) (p : X→Y) (hp : Measurable p) : Kernel X where
  W := fun z => K.W (p z.1,p z.2)
  measurable_W := K.measurable_W.comp (hp.prodMap hp)
  nonneg := fun _ => K.nonneg _
  le_one := fun _ => K.le_one _
  symm := fun _ _ => K.symm _ _

theorem push_submeasure_energy (K : Kernel Y) (p : X→Y) (hp : Measurable p)
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (∫ z, (pullKernel K p hp).W z ∂μ.prod ν) =
      ∫ z, K.W z ∂(μ.map p).prod (ν.map p) := by
  rw [Measure.map_prod_map μ ν hp hp]
  rw [integral_map (hp.prodMap hp).aemeasurable K.measurable_W.aestronglyMeasurable]
  rfl

theorem pull_energy (K : Kernel Y) (p : X→Y)
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hp : MeasurePreserving p μ ν) (f g : Y→ℝ) (hf : Measurable f) (hg : Measurable g) :
    energyPair μ (pullKernel K p hp.measurable) (f ∘ p) (g ∘ p) =
      energyPair ν K f g := by
  have hh : MeasurePreserving (Prod.map p p) (μ.prod μ) (ν.prod ν) := hp.prod hp
  have hm : Measurable (fun z : Y×Y => f z.1*g z.2*K.W z) :=
    ((hf.comp measurable_fst).mul (hg.comp measurable_snd)).mul K.measurable_W
  unfold energyPair
  rw [← hh.map_eq,integral_map hh.measurable.aemeasurable hm.aestronglyMeasurable]
  rfl

theorem pull_triangle (K L M : Kernel Y) (p : X→Y)
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hp : MeasurePreserving p μ ν) :
    t3 μ (pullKernel K p hp.measurable) (pullKernel L p hp.measurable)
      (pullKernel M p hp.measurable)=t3 ν K L M := by
  have hh : MeasurePreserving (Prod.map (Prod.map p p) p) ((μ.prod μ).prod μ)
      ((ν.prod ν).prod ν) := (hp.prod hp).prod hp
  unfold t3
  rw [← hh.map_eq,integral_map hh.measurable.aemeasurable (mixed_meas K L M).aestronglyMeasurable]
  rfl

#print axioms pull_energy
#print axioms pull_triangle
end SparseHalfGraphon
