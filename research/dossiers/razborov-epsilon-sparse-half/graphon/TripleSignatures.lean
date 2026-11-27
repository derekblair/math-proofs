import SignatureAllocation
import SaturatedOrthogonal

open Set MeasureTheory
namespace SparseHalfCountableEndpoint
variable {X : Type*} [MeasurableSpace X]
variable (ν : Measure X) [IsFiniteMeasure ν]

def tripleCell (S T U : Set X) (j : Bool×Bool×Bool) : Set X :=
  (side S j.1 ∩ side T j.2.1) ∩ side U j.2.2

lemma tripleCell_meas (S T U : Set X) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hU : MeasurableSet U) (j : Bool×Bool×Bool) : MeasurableSet (tripleCell S T U j) :=
  ((side_meas S hS j.1).inter (side_meas T hT j.2.1)).inter (side_meas U hU j.2.2)

lemma tripleCell_disjoint (S T U : Set X) {j k : Bool×Bool×Bool} (h : j≠k) :
    Disjoint (tripleCell S T U j) (tripleCell S T U k) := by
  by_cases e : (j.1,j.2.1)=(k.1,k.2.1)
  · have d : j.2.2≠k.2.2 := fun hh => h
      (Prod.ext (congrArg (fun z : Bool×Bool => z.1) e) (Prod.ext (congrArg (fun z : Bool×Bool => z.2) e) hh))
    exact (side_disjoint U d).mono inter_subset_right inter_subset_right
  · exact (sigCell_disjoint S T e).mono inter_subset_left inter_subset_left

/-- A unit pair-intersection makes all four cells of that pair unit. -/
def Orthogonal (S T : Set X) : Prop :=
  ∀ j : Bool×Bool, ν.real (sigCell S T j)=1

theorem orthogonal_of_overlap (S T : Set X) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hV : ν.real univ=4) (hS' : ν.real S=2) (hT' : ν.real T=2)
    (he : ν.real (S∩T)=1) : Orthogonal ν S T := by
  obtain ⟨_,_,e3,e1,e2⟩ := four_cell_mass ν S T hS hT hV hS' hT'
  have e0 : ν.real (sigCell S T (false,false))=1 := by
    rw [←e3]; exact he
  rw [e0] at e1 e2 e3
  rintro ⟨a,b⟩
  cases a <;> cases b
  · exact e0
  · linarith
  · linarith
  · exact e3

/-- Pairwise orthogonality determines every joint mass from the parity
of its pattern. This is an exact measurable statement, not a finite
vertex approximation. -/
theorem triple_parity (S T U : Set X)
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hU : MeasurableSet U)
    (hST : Orthogonal ν S T) (hSU : Orthogonal ν S U) (hTU : Orthogonal ν T U) :
    let x := ν.real (tripleCell S T U (false,false,false))
    ∀ a b c : Bool, ν.real (tripleCell S T U (a,b,c))=
      if xor (xor a b) c then 1-x else x := by
  intro x
  let w := fun a b c : Bool => ν.real (tripleCell S T U (a,b,c))
  have ab (a b : Bool) : w a b false + w a b true=1 := by
    have eq := split_real ν (sigCell S T (a,b)) U (sigCell_meas S T hS hT _) hU
    rw [hST (a,b)] at eq
    exact (add_comm _ _).trans eq
  have ac (a c : Bool) : w a false c + w a true c=1 := by
    have eq := split_real ν (sigCell S U (a,c)) T (sigCell_meas S U hS hU _) hT
    rw [hSU (a,c)] at eq
    dsimp [sigCell,side] at eq
    have eq' := eq
    change ν.real ((side S a ∩ side U c)∩T)+ν.real ((side S a ∩ side U c)∩Tᶜ)=1 at eq'
    dsimp [w,tripleCell]
    simpa only [inter_assoc, inter_left_comm, inter_comm] using (add_comm _ _).trans eq'
  have bc (b c : Bool) : w false b c + w true b c=1 := by
    have eq := split_real ν (sigCell T U (b,c)) S (sigCell_meas T U hT hU _) hS
    rw [hTU (b,c)] at eq
    change ν.real ((side T b ∩ side U c)∩S)+ν.real ((side T b ∩ side U c)∩Sᶜ)=1 at eq
    dsimp [w,tripleCell]
    simpa only [inter_assoc, inter_left_comm, inter_comm] using (add_comm _ _).trans eq
  obtain ⟨d011,d101,d110,d001,d010,d100,d111⟩ := SparseHalfSaturatedOrthogonal.parity
    (w false false false) (w false false true) (w false true false) (w false true true)
    (w true false false) (w true false true) (w true true false) (w true true true)
    (ab false false) (ab false true) (ab true false) (ab true true)
    (ac false false) (ac false true) (ac true false) (ac true true)
    (bc false false) (bc false true) (bc true false) (bc true true)
  intro a b c
  cases a <;> cases b <;> cases c
  · rfl
  · exact d001
  · exact d010
  · exact d011
  · exact d100
  · exact d101
  · exact d110
  · exact d111

#print axioms triple_parity
end SparseHalfCountableEndpoint
