import StepRigidity
import PetersenParity

open Set MeasureTheory SparseHalfGraphon
namespace SparseHalfCountableEndpoint
open PetersenParity
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem petersen_sym : ∀ i j, adjacent i j=adjacent j i := by decide

/-- Equality against the completed uniform Petersen bank follows from
the eight explicitly checked tight half testers. -/
theorem petersen_step_rigidity (K : Kernel X) (P : Fin 10→Set X)
    (B : Cells P) (cover : ∀ᵐ x ∂μ,∃ i,x∈P i) (mass : ∀ i,μ.real (P i)=1/10)
    (zeros : ∀ i j,adjacent i j=false →
      ∀ᵐ z ∂(μ.restrict (P i)).prod (μ.restrict (P j)),K.W z=0) :
    (∃ H : Half μ,halfEnergy μ K H<1/50) ∨
      K.W =ᵐ[μ.prod μ] (stepKernel P adjacent B petersen_sym).W := by
  classical
  apply step_rigidity P adjacent μ B petersen_sym K cover zeros
  intro i j h
  obtain ⟨s,hs,is,js⟩ := each_edge_seen i j h
  obtain ⟨sm,se⟩ := tight_five s hs
  let q := fun k : Fin 10 => if k∈s then (1:ℝ)/10 else 0
  have qm : (∑ k,q k)=1/2 := by
    calc
      (∑ k,q k) = ∑ k∈s,(1:ℝ)/10 := by
        rw [←Finset.sum_filter]
        simp
      _ = 1/2 := by norm_num [Finset.sum_const,sm,nsmul_eq_mul]
  have qcost : (∑ a : Fin 10×Fin 10,
      q a.1*q a.2*(if adjacent a.1 a.2 then 1 else 0))/2≤1/50 := by
    let E := (s ×ˢ s).filter fun z => adjacent z.1 z.2=true
    have ecard : E.card=4 := se
    have point (a : Fin 10×Fin 10) :
        q a.1*q a.2*(if adjacent a.1 a.2 then 1 else 0) =
          if a∈E then (1:ℝ)/100 else 0 := by
      by_cases a1 : a.1∈s <;> by_cases a2 : a.2∈s <;>
        cases T : adjacent a.1 a.2 <;> norm_num [q,E,Finset.mem_product,a1,a2,T]
    simp only [point]
    rw [←Finset.sum_filter]
    have v : (Finset.univ.filter (fun a => a∈E))=E := by simp
    rw [v]
    norm_num [Finset.sum_const,ecard,nsmul_eq_mul]
  refine ⟨q,fun t => ?_,qm,by simp [q,is],by simp [q,js],qcost⟩
  rw [mass]
  by_cases ht : t∈s <;> norm_num [q,ht]

#print axioms petersen_step_rigidity
end SparseHalfCountableEndpoint
