import KernelBlockMeans

open Set MeasureTheory Function
open scoped BigOperators
namespace SparseHalfGraphon

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable {S T : Type*} [Fintype T] [DecidableEq S]
variable [MeasurableSpace T] [MeasurableSingletonClass T]

lemma parent_cell_union (c : X → S) (d : X → T) (p : T → S)
    (hp : ∀ x, c x = p (d x)) (i : S) :
    cell c i = ⋃ j : {z // p z = i}, cell d j.val := by
  ext x
  constructor
  · intro h
    have h' : c x = i := h
    exact mem_iUnion.mpr ⟨⟨d x, (hp x).symm.trans h'⟩,rfl⟩
  · intro h
    obtain ⟨j,hj⟩ := mem_iUnion.mp h
    have h' : d x = j.val := hj
    exact (hp x).trans ((congrArg p h').trans j.property)

/-- Restricting a fine cell-constant function to a coarse cell
integrates exactly as a finite sum over the children. -/
theorem integral_parent_cell (c : X → S) (d : X → T) (p : T → S)
    (hd : Measurable d) (hp : ∀ x, c x = p (d x))
    (v : T → ℝ) (i : S) :
    (∫ x in cell c i, v (d x) ∂μ) = ∑ j with p j = i, μ.real (cell d j)*v j := by
  rw [parent_cell_union c d p hp i]
  have hm (j : {z // p z = i}) : MeasurableSet (cell d j.val) :=
    hd (measurableSet_singleton _)
  have hD : Pairwise (Disjoint on fun j : {z // p z = i} => cell d j.val) := by
    intro j k hjk
    apply Set.disjoint_left.mpr
    intro x hx hy
    have h₁ : d x = j.val := hx
    have h₂ : d x = k.val := hy
    exact hjk (Subtype.ext (h₁.symm.trans h₂))
  change (∫ x in (⋃ j : {z // p z = i}, cell d j.val), (v ∘ d) x ∂μ) = _
  rw [integral_iUnion_fintype hm hD
    (fun _ => (bMeas_integrable μ (bmeas_comp_finite d hd v)).integrableOn)]
  have hI (j : {z // p z = i}) :
      (∫ x in cell d j.val, v (d x) ∂μ) = μ.real (cell d j.val)*v j.val := by
    rw [setIntegral_congr_fun (hm j) (show EqOn (fun x => v (d x)) (fun _ => v j.val) (cell d j.val) from
      fun x hx => congrArg v hx), setIntegral_const, smul_eq_mul]
  simp only [Function.comp_apply, hI]
  exact (Finset.sum_subtype (p := fun j => p j = i) (Finset.univ.filter (fun j => p j = i)) (fun _ => by simp) (fun j => μ.real (cell d j) * v j)).symm

#print axioms integral_parent_cell
end SparseHalfGraphon
