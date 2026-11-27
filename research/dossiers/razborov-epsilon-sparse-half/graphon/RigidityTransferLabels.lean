import PetersenKernel
import LargeIsolateCycle
import StabilityExamples

open Set MeasureTheory SparseHalfGraphon
namespace SparseHalfCountableEndpoint
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

def petersenTransferPerm : Fin 10→Fin 10 :=
  ![0,1,2,3,9,4,8,5,7,6]

def petersenTransferInv : Fin 10→Fin 10 :=
  ![0,1,2,3,5,7,9,8,6,4]

theorem petersen_transfer_left : ∀ i,petersenTransferInv (petersenTransferPerm i)=i := by decide
theorem petersen_transfer_right : ∀ i,petersenTransferPerm (petersenTransferInv i)=i := by decide

theorem petersen_transfer_adj : ∀ i j,
    PetersenParity.adjacent i j=PetersenStability.adj
      (SparseHalfStability.pEmbed (petersenTransferPerm i))
      (SparseHalfStability.pEmbed (petersenTransferPerm j)) := by decide

theorem c5_transfer_adj : ∀ i j,c5 i j=C5Stability.adj i j := by decide

theorem petersen_label_for_transfer (K : Kernel X) (g : X→Fin 10)
    (gm : Measurable g) (gb : ∀ i,μ.real (cell g i)=1/10)
    (ge : K.W =ᵐ[μ.prod μ] (fun z => edgeReal (PetersenParity.adjacent (g z.1) (g z.2)))) :
    ∃ f : X→Fin 10, Measurable f ∧ (∀ i,μ.real (cell f i)=1/10) ∧
      K.W =ᵐ[μ.prod μ] (fun z => edgeReal (PetersenStability.adj
        (SparseHalfStability.pEmbed (f z.1)) (SparseHalfStability.pEmbed (f z.2)))) := by
  let f := fun x => petersenTransferPerm (g x)
  have fm : Measurable f := (measurable_of_countable petersenTransferPerm).comp gm
  refine ⟨f,fm,?_,?_⟩
  · intro i
    have e : cell f i=cell g (petersenTransferInv i) := by
      ext x
      change petersenTransferPerm (g x)=i ↔ g x=petersenTransferInv i
      constructor
      · intro a
        exact (petersen_transfer_left (g x)).symm.trans (congrArg petersenTransferInv a)
      · intro a; rw [a,petersen_transfer_right]
    rw [e,gb]
  · filter_upwards [ge] with z hz
    exact hz.trans (congrArg edgeReal (petersen_transfer_adj _ _))

/-- The C5 equality branch in exactly the final finite-stability labeling. -/
theorem isolate_label_for_transfer (K : Kernel X) (A S P Q : Set X)
    (B : Cells (isolateCells A S P Q)) (m : ∀ i, μ.real (isolateCells A S P Q i)=1/5)
    (eq : K.W =ᵐ[μ.prod μ] (stepKernel (isolateCells A S P Q) c5 B c5_sym).W) :
    ∃ g : X→Fin 5, Measurable g ∧ (∀ i,μ.real (cell g i)=1/5) ∧
      K.W =ᵐ[μ.prod μ] (fun z => edgeReal (C5Stability.adj (g z.1) (g z.2))) := by
  obtain ⟨g,gm,gb,ge⟩ := binary_label_of_step _ μ c5 B c5_sym K
    (ae_of_all _ (isolate_cover A S P Q)) eq
  refine ⟨g,gm,fun i => (gb i).trans (m i),?_⟩
  filter_upwards [ge] with z hz
  exact hz.trans (congrArg edgeReal (c5_transfer_adj _ _))

#print axioms petersen_label_for_transfer
#print axioms isolate_label_for_transfer
end SparseHalfCountableEndpoint
