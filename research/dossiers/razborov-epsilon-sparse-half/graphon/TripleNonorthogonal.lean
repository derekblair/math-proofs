import TripleStrict

open Set MeasureTheory
namespace SparseHalfCountableEndpoint
variable {X : Type*} [MeasurableSpace X]
variable (ν : Measure X) [IsFiniteMeasure ν]

private theorem choose_side (S T : Set X) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hS' : ν.real S=2) :
    ∃ b : Bool, ν.real (S∩side T b)=min (ν.real (S∩T)) (2-ν.real (S∩T)) := by
  have split := split_real ν S T hS hT
  by_cases h : ν.real (S∩T)≤2-ν.real (S∩T)
  · exact ⟨true,(min_eq_left h).symm⟩
  · refine ⟨false,?_⟩
    rw [side_false,min_eq_right (le_of_not_ge h)]
    linarith

/-- A nonorthogonal pair among three unit pairs gives a strict half:
take an entire one-coordinate anchor half and choose cheaper outside
orientations independently. -/
theorem nonorthogonal_half (S T U : Set X)
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hU : MeasurableSet U)
    (hS' : ν.real S=2) (neq : ν.real (S∩T)≠1) : UnitHalf ν S T U := by
  obtain ⟨b,bh⟩ := choose_side ν S T hS hT hS'
  obtain ⟨c,ch⟩ := choose_side ν S U hS hU hS'
  let f := S.indicator (fun _ => (1:ℝ))
  have m : Measurable f := measurable_const.indicator hS
  have unit (x : X) : 0≤f x ∧ f x≤1 := by
    by_cases hx : x∈S <;> simp [f,hx]
  refine ⟨(false,b,c),f,m,unit,?_,?_⟩
  · unfold f
    rw [integral_indicator hS,setIntegral_const,smul_eq_mul,mul_one]
    exact hS'
  · have e (x : X) :
      threeLoad Sᶜ (side T b) (side U c) x*f x =
        (S∩side T b).indicator (fun _ => 1) x +
        (S∩side U c).indicator (fun _ => 1) x := by
      classical
      by_cases hs : x∈S <;> by_cases ht : x∈side T b <;> by_cases hu : x∈side U c <;>
        simp [threeLoad,f,hs,ht,hu]
    change (∫ x,threeLoad Sᶜ (side T b) (side U c) x*f x ∂ν)<2
    simp only [e]
    rw [integral_add ((integrable_const _).indicator (hS.inter (side_meas T hT b)))
      ((integrable_const _).indicator (hS.inter (side_meas U hU c)))]
    rw [integral_indicator (hS.inter (side_meas T hT b)),
      integral_indicator (hS.inter (side_meas U hU c))]
    simp only [setIntegral_const,smul_eq_mul,mul_one]
    rw [bh,ch]
    exact SparseHalfSaturatedOrthogonal.nonorthogonal _ _ neq

private theorem unitHalf_swap_first (S T U : Set X) (h : UnitHalf ν T S U) : UnitHalf ν S T U := by
  obtain ⟨⟨a,b,c⟩,f,fm,fb,fs,fc⟩ := h
  refine ⟨(b,a,c),f,fm,fb,fs,?_⟩
  simpa [threeLoad,add_assoc,add_comm,add_left_comm] using fc

private theorem unitHalf_swap_last (S T U : Set X) (h : UnitHalf ν S U T) : UnitHalf ν S T U := by
  obtain ⟨⟨a,b,c⟩,f,fm,fb,fs,fc⟩ := h
  refine ⟨(a,c,b),f,fm,fb,fs,?_⟩
  simpa [threeLoad,add_assoc,add_comm,add_left_comm] using fc

/-- The full three-unit-pair anchor theorem: either a strict normalized
half exists, or the four occupied anchor signatures are a parity class
and each has mass one. -/
theorem three_unit_rigidity (S T U : Set X)
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hU : MeasurableSet U)
    (hV : ν.real univ=4) (hS' : ν.real S=2) (hT' : ν.real T=2) (hU' : ν.real U=2) :
    UnitHalf ν S T U ∨ ∃ v : Bool,
      ∀ a b c : Bool, ν.real (tripleCell S T U (a,b,c))=
        if xor (xor a b) c=v then (1:ℝ) else 0 := by
  by_cases ST : ν.real (S∩T)=1
  · by_cases SU : ν.real (S∩U)=1
    · by_cases TU : ν.real (T∩U)=1
      · rcases orthogonal_strict_or_parity ν S T U hS hT hU
          (orthogonal_of_overlap ν S T hS hT hV hS' hT' ST)
          (orthogonal_of_overlap ν S U hS hU hV hS' hU' SU)
          (orthogonal_of_overlap ν T U hT hU hV hT' hU' TU) with cert | ⟨e,parity⟩
        · exact Or.inl cert
        · right
          rcases e with x0|x1
          · refine ⟨true,fun a b c => ?_⟩
            rw [parity,x0,sub_zero]
          · refine ⟨false,fun a b c => ?_⟩
            rw [parity,x1,sub_self]
            cases xor (xor a b) c <;> simp
      · exact Or.inl (unitHalf_swap_first ν S T U (unitHalf_swap_last ν T S U
          (nonorthogonal_half ν T U S hT hU hS hT' TU)))
    · exact Or.inl (unitHalf_swap_last ν S T U (nonorthogonal_half ν S U T hS hU hT hS' SU))
  · exact Or.inl (nonorthogonal_half ν S T U hS hT hU hS' ST)

#print axioms three_unit_rigidity
end SparseHalfCountableEndpoint
