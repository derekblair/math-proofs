import StepRigidity

open Set MeasureTheory SparseHalfGraphon
namespace SparseHalfCountableEndpoint

/-- Fixed cycle in the order A₊, P, Q, A₋, isolated-outside pool. -/
def c5 (i j : Fin 5) : Bool := (i+1==j) || (j+1==i)

theorem c5_sym (i j : Fin 5) : c5 i j=c5 j i := by simp [c5,Bool.or_comm]

def c5Weight (i j : Fin 5) : ℕ :=
  if j=i ∨ j=i+3 then 2 else if j=i+1 then 1 else 0

noncomputable def c5Fill (i j : Fin 5) : ℝ := (c5Weight i j : ℝ)/10

theorem c5EdgeTester : ∀ i j : Fin 5,c5 i j=true →
    ∃ k : Fin 5, 0<c5Weight k i ∧ 0<c5Weight k j := by decide

theorem c5Fill_cap (i j : Fin 5) : 0≤c5Fill i j ∧ c5Fill i j≤1/5 := by
  unfold c5Fill c5Weight
  split
  · norm_num
  · split <;> norm_num

theorem c5Fill_total (i : Fin 5) : (∑ j,c5Fill i j)=1/2 := by
  fin_cases i <;> norm_num [c5Fill,c5Weight,Fin.sum_univ_succ]

theorem c5Fill_cost (i : Fin 5) :
    (∑ a : Fin 5×Fin 5,c5Fill i a.1*c5Fill i a.2*(if c5 a.1 a.2 then 1 else 0))/2 = 1/50 := by
  fin_cases i <;> norm_num [Fintype.sum_prod_type,Fin.sum_univ_succ,c5Fill,c5Weight,c5]

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- The completed equal-cell five-cycle is rigid against every missing
rectangle, including between the outside isolates and either anchor half. -/
theorem c5_step_rigidity (K : Kernel X) (P : Fin 5→Set X)
    (B : Cells P) (cover : ∀ᵐ x ∂μ,∃ i,x∈P i) (mass : ∀ i,μ.real (P i)=1/5)
    (zeros : ∀ i j,c5 i j=false →
      ∀ᵐ z ∂(μ.restrict (P i)).prod (μ.restrict (P j)),K.W z=0) :
    (∃ H : Half μ,halfEnergy μ K H<1/50) ∨
      K.W =ᵐ[μ.prod μ] (stepKernel P c5 B c5_sym).W := by
  apply step_rigidity P c5 μ B c5_sym K cover zeros
  intro i j h
  obtain ⟨k,ki,kj⟩ := c5EdgeTester i j h
  have cPos (t : Fin 5) (hh : 0<c5Weight k t) : 0<c5Fill k t := by
    unfold c5Fill
    exact div_pos (by exact_mod_cast hh) (by norm_num)
  refine ⟨c5Fill k,fun t => ?_, c5Fill_total k,cPos i ki,cPos j kj,(c5Fill_cost k).le⟩
  rw [mass]
  exact c5Fill_cap k t

#print axioms c5_step_rigidity
end SparseHalfCountableEndpoint
