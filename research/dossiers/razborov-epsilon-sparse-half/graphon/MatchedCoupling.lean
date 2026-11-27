import CouplingFractional

open MeasureTheory Set
open scoped ENNReal
namespace SparseHalfGraphon

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Join two prescribed equal-mass pieces, with a harmless zero convention. -/
noncomputable def joinPiece (μ : Measure X) (ν : Measure Y) : Measure (X×Y) :=
  (ν univ)⁻¹ • μ.prod ν

lemma joinPiece_fst (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (he : μ univ=ν univ) :
    (joinPiece μ ν).map Prod.fst=μ := by
  by_cases hz : ν univ=0
  · have hm : μ=0 := Measure.measure_univ_eq_zero.mp (he.trans hz)
    simp [joinPiece,hm]
  · unfold joinPiece
    rw [Measure.map_smul _ measurable_fst.aemeasurable,Measure.map_fst_prod,smul_smul,
      ENNReal.inv_mul_cancel hz (measure_ne_top ν univ),one_smul]

lemma joinPiece_snd (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (he : μ univ=ν univ) :
    (joinPiece μ ν).map Prod.snd=ν := by
  by_cases hz : ν univ=0
  · have hν : ν=0 := Measure.measure_univ_eq_zero.mp hz
    simp [joinPiece,hν]
  · unfold joinPiece
    rw [Measure.map_smul _ measurable_snd.aemeasurable,Measure.map_snd_prod,he,smul_smul,
      ENNReal.inv_mul_cancel hz (measure_ne_top ν univ),one_smul]

/-- A mixture of matched pieces has exactly the two given marginals. -/
theorem join_family {I : Type*} (μ : I→Measure X) (ν : I→Measure Y)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, IsFiniteMeasure (ν i)]
    (he : ∀ i, μ i univ=ν i univ) :
    let π := Measure.sum (fun i => joinPiece (μ i) (ν i))
    MeasurePreserving Prod.fst π (Measure.sum μ) ∧ MeasurePreserving Prod.snd π (Measure.sum ν) := by
  dsimp
  constructor
  · refine ⟨measurable_fst,?_⟩
    rw [Measure.map_sum measurable_fst.aemeasurable]
    simp only [joinPiece_fst _ _ (he _)]
  · refine ⟨measurable_snd,?_⟩
    rw [Measure.map_sum measurable_snd.aemeasurable]
    simp only [joinPiece_snd _ _ (he _)]

#print axioms join_family
end SparseHalfGraphon
