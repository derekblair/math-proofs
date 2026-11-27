import FiberIntegrals

open Set MeasureTheory Function
open scoped BigOperators
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable {S T : Type*} [Fintype T] [DecidableEq S]
variable [MeasurableSpace T] [MeasurableSingletonClass T]

/-- Averaging a fine mean over a coarser partition gives the coarse mean
of the unaveraged function. This uses exact means on null cells too. -/
theorem meanBlock_tower (c : X → S) (d : X → T) (p : T → S)
    (hd : Measurable d) (hp : ∀ x, c x = p (d x)) (W : X → ℝ) (hW : BMeas W) :
    meanBlock μ c (meanBlock μ d W) = meanBlock μ c W := by
  funext x
  unfold meanBlock meanCell
  congr 1
  change (∫ y in cell c (c x), meanBlock μ d W y ∂μ) =
    (∫ y in cell c (c x), W y ∂μ)
  rw [show (fun y => meanBlock μ d W y) = (fun y => meanCell μ d W (d y)) from rfl,
    integral_parent_cell c d p hd hp]
  set i := c x
  rw [parent_cell_union c d p hp i]
  have hm (j : {z // p z = i}) : MeasurableSet (cell d j.val) :=
    hd (measurableSet_singleton _)
  have hD : Pairwise (Disjoint on fun j : {z // p z = i} => cell d j.val) := by
    intro j k hjk
    apply Set.disjoint_left.mpr
    intro y hy hz
    have h₁ : d y = j.val := hy
    have h₂ : d y = k.val := hz
    exact hjk (Subtype.ext (h₁.symm.trans h₂))
  rw [integral_iUnion_fintype hm hD (fun _ => (bMeas_integrable μ hW).integrableOn)]
  simp_rw [mean_cell_exact]
  exact Finset.sum_subtype (p := fun j => p j = i)
    (Finset.univ.filter (fun j => p j = i)) (fun _ => by simp) (fun j => ∫ y in cell d j, W y ∂μ)

#print axioms meanBlock_tower
end SparseHalfGraphon
