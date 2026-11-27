import CouplingCut

open MeasureTheory Set Function
namespace SparseHalfGraphon

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSingletonClass Y]

def atomLabels (μ : Measure X) (p : X→Y) : Set Y :=
  {y | 0<μ (p ⁻¹' {y})}

/-- Positive-mass row fibers are countable. -/
theorem atomLabels_countable (μ : Measure X) [IsFiniteMeasure μ] (p : X→Y)
    (hp : Measurable p) :
    (atomLabels μ p).Countable := by
  apply Measure.countable_meas_pos_of_disjoint_iUnion
    (As := fun y => p ⁻¹' {y})
  · intro y
    exact hp (measurableSet_singleton y)
  · intro y z hyz
    apply Set.disjoint_left.mpr
    intro x hx hz
    have hx' : p x=y := hx
    have hz' : p x=z := hz
    exact hyz (hx'.symm.trans hz')

/-- Almost every entry satisfying a row matching relation lands in an
atomic fiber. A version with involutive matching yields both endpoints. -/
theorem relation_on_atoms (μ : Measure X) [IsFiniteMeasure μ]
    (p : X→Y) (hp : Measurable p) (C : Y→Y)
    (hrel : MeasurableSet {z:X×X | p z.2=C (p z.1)}) :
    ∀ᵐ z ∂μ.prod μ, p z.2=C (p z.1) → p z.2∈atomLabels μ p := by
  have ha : MeasurableSet (atomLabels μ p) := (atomLabels_countable μ p hp).measurableSet
  have hm : MeasurableSet {z:X×X | p z.2=C (p z.1) → p z.2∈atomLabels μ p} := by
    have he : {z:X×X | p z.2=C (p z.1) → p z.2∈atomLabels μ p}=
        {z:X×X | p z.2=C (p z.1)}ᶜ ∪ (p ∘ Prod.snd) ⁻¹' atomLabels μ p := by
      ext z
      simp only [mem_setOf_eq,mem_union,mem_compl_iff,mem_preimage,Function.comp_apply,imp_iff_not_or]
    rw [he]
    exact hrel.compl.union ((hp.comp measurable_snd) ha)
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  apply ae_of_all
  intro x
  by_cases ha : C (p x)∈atomLabels μ p
  · exact ae_of_all _ (fun y h => h.symm ▸ ha)
  · have hz : μ (p ⁻¹' {C (p x)})=0 := by
      change ¬ 0<μ (p ⁻¹' {C (p x)}) at ha
      exact le_antisymm (not_lt.mp ha) bot_le
    have hno : ∀ᵐ y ∂μ, y ∉ p ⁻¹' {C (p x)} := ae_iff.mpr (by
      have he : {y | ¬ (y ∉ p ⁻¹' {C (p x)})}=p ⁻¹' {C (p x)} := by
        ext y
        simp only [not_not,mem_setOf_eq]
      rwa [he])
    filter_upwards [hno] with y hy he
    exact False.elim (hy he)

#print axioms atomLabels_countable
#print axioms relation_on_atoms
end SparseHalfGraphon
