import StepRigidity
import FiniteKernelModel
import BlockMeans

open Set MeasureTheory SparseHalfGraphon
namespace SparseHalfCountableEndpoint
variable {X : Type*} [MeasurableSpace X]
variable {I : Type*} [Fintype I] [Inhabited I] [MeasurableSpace I]
variable (P : I→Set X)

noncomputable def cellLabel : X→I := by
  classical
  exact fun x =>
    if h : ∃ i, x∈P i then h.choose else default

lemma cellLabel_on (B : Cells P) {i : I} {x : X} (hi : x∈P i) : cellLabel P x=i := by
  have h : ∃ i,x∈P i := ⟨i,hi⟩
  rw [cellLabel,dite_eq_left h]
  by_contra! ne
  exact Set.disjoint_left.mp (B.disjoint ne) (h.choose_spec) hi

lemma cellLabel_meas (B : Cells P) : Measurable (cellLabel P) := by
  classical
  apply measurable_to_countable'
  intro i
  have h (x : X) : cellLabel P x=i ↔ x∈P i ∨ (i=default ∧ x∉⋃ j,P j) := by
    by_cases e : ∃ i,x∈P i
    · have eu : x∈⋃ j,P j := mem_iUnion.mpr e
      simp only [eu,not_true_eq_false,and_false,or_false]
      constructor
      · intro eq
        rw [cellLabel,dite_eq_left e] at eq
        exact eq ▸ e.choose_spec
      · exact cellLabel_on P B
    · have eu : x∉⋃ j,P j := fun h => e (mem_iUnion.mp h)
      rw [cellLabel,dite_eq_right e]
      simp [eu,show x∉P i from fun hi => e ⟨i,hi⟩,eq_comm]
  have eq : cellLabel P ⁻¹' {i} = P i ∪ (if i=default then (⋃ j,P j)ᶜ else ∅) := by
    ext x
    simp only [mem_preimage,mem_singleton_iff,mem_union,h]
    split <;> simp_all
  rw [eq]
  exact (B.meas i).union (by split; exact (MeasurableSet.iUnion B.meas).compl; exact MeasurableSet.empty)

variable (μ : Measure X) [IsFiniteMeasure μ]

lemma cellLabel_mass (B : Cells P) (cover : ∀ᵐ x∂μ,∃ i,x∈P i) (i : I) :
    μ.real (cell (cellLabel P) i)=μ.real (P i) := by
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [cover] with x ⟨j,hj⟩
  change (cellLabel P x=i) = (x∈P i)
  apply propext
  constructor
  · intro h
    have e := (cellLabel_on P B hj).symm.trans h
    exact e ▸ hj
  · exact cellLabel_on P B

/-- Format a balanced step limit as an actual measurable label, assigning
the null complement a harmless default. This is the final-transfer API. -/
theorem binary_label_of_step (e : I→I→Bool) (B : Cells P) (sym : ∀ i j,e i j=e j i)
    (K : Kernel X) (cover : ∀ᵐ x∂μ,∃ i,x∈P i)
    (eq : K.W =ᵐ[μ.prod μ] (stepKernel P e B sym).W) :
    ∃ g : X→I, Measurable g ∧ (∀ i, μ.real (cell g i)=μ.real (P i)) ∧
      K.W =ᵐ[μ.prod μ] (fun z => edgeReal (e (g z.1) (g z.2))) := by
  refine ⟨cellLabel P,cellLabel_meas P B,cellLabel_mass P μ B cover,?_⟩
  filter_upwards [eq,(Measure.quasiMeasurePreserving_fst (μ:=μ) (ν:=μ)).ae cover,
    (Measure.quasiMeasurePreserving_snd (μ:=μ) (ν:=μ)).ae cover] with ⟨x,y⟩ hxy ⟨i,hi⟩ ⟨j,hj⟩
  change K.W (x,y)=stepW P e (x,y) at hxy
  rw [hxy,stepW_on P e B i j hi hj]
  change _=edgeReal (e (cellLabel P x) (cellLabel P y))
  rw [cellLabel_on P B hi,cellLabel_on P B hj]
  rfl

#print axioms binary_label_of_step
end SparseHalfCountableEndpoint
