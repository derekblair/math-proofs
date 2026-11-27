import SetAllocation
import MixedOrientation

open Set MeasureTheory
namespace SparseHalfCountableEndpoint

variable {X : Type*} [MeasurableSpace X]
variable (ν : Measure X) [IsFiniteMeasure ν]

/-- The ambient measure is the restricted measure of the independent A
anchor; the signatures need only be measurable, not atomless. -/
def side (S : Set X) (b : Bool) : Set X := if b then S else Sᶜ

def sigCell (S T : Set X) (j : Bool×Bool) : Set X :=
  side S j.1 ∩ side T j.2

@[simp] lemma side_false (S : Set X) : side S false = Sᶜ := rfl
@[simp] lemma side_true (S : Set X) : side S true = S := rfl

lemma side_meas (S : Set X) (hS : MeasurableSet S) (b : Bool) :
    MeasurableSet (side S b) := by cases b <;> simp [hS,hS.compl]

lemma sigCell_meas (S T : Set X) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (j : Bool×Bool) : MeasurableSet (sigCell S T j) :=
  (side_meas S hS j.1).inter (side_meas T hT j.2)

lemma side_disjoint (S : Set X) {a b : Bool} (h : a≠b) :
    Disjoint (side S a) (side S b) := by
  cases a <;> cases b <;> simp_all [disjoint_compl_left,disjoint_compl_right]

lemma sigCell_disjoint (S T : Set X) {j k : Bool×Bool} (h : j≠k) :
    Disjoint (sigCell S T j) (sigCell S T k) := by
  by_cases h₁ : j.1=k.1
  · have h₂ : j.2≠k.2 := fun hh => h (Prod.ext h₁ hh)
    exact (side_disjoint T h₂).mono inter_subset_right inter_subset_right
  · exact (side_disjoint S h₁).mono inter_subset_left inter_subset_left

lemma split_real (S T : Set X) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ν.real (S∩T) + ν.real (S∩Tᶜ) = ν.real S := by
  have hU : (S∩T)∪(S∩Tᶜ) = S := by ext x; by_cases h : x∈T <;> simp [h]
  have hd : Disjoint (S∩T) (S∩Tᶜ) :=
    disjoint_compl_right.mono inter_subset_right inter_subset_right
  rw [←measureReal_union hd (hS.inter hT.compl)]
  rw [hU]

/-- Exact four-cell area identities on a finite-measure anchor. -/
theorem four_cell_mass (S T : Set X) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hV : ν.real univ=4) (hS' : ν.real S=2) (hT' : ν.real T=2) :
    let x := ν.real (sigCell S T (false,false))
    0≤x ∧ x≤2 ∧
      ν.real (sigCell S T (true,true))=x ∧
      ν.real (sigCell S T (true,false))=2-x ∧
      ν.real (sigCell S T (false,true))=2-x := by
  intro x
  have a := split_real ν S T hS hT
  have b := split_real ν Sᶜ T hS.compl hT
  have c := split_real ν T S hT hS
  have d := measureReal_add_measureReal_compl (μ:=ν) hS
  rw [inter_comm T S,inter_comm T Sᶜ] at c
  have n : 0≤ν.real (Sᶜ∩T) := measureReal_nonneg
  dsimp [x,sigCell,side]
  exact ⟨measureReal_nonneg,by linarith,by linarith,by linarith,by linarith⟩

#print axioms four_cell_mass
end SparseHalfCountableEndpoint
