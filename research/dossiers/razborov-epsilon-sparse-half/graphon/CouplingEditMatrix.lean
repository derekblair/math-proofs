import FiberIntegrals
import EditRoundExistence
open MeasureTheory Set Function
open scoped BigOperators
namespace SparseHalfGraphon
open SparseHalfEditRound

variable {X V I : Type*} [MeasurableSpace X]
    [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
variable (μ : Measure X) [IsFiniteMeasure μ]

noncomputable def couplingMatrix (f : X → V) (g : X → I) (v : V) (i : I) : ℝ :=
  (Fintype.card V : ℝ)*μ.real (cell f v ∩ cell g i)

private theorem disjoint_cells {A : Type*} (f : X → A) :
    Pairwise (Disjoint on fun a => cell f a) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro x hx hx'
  exact hab ((show f x=a from hx).symm.trans hx')

theorem coupling_row (f : X → V) (g : X → I) (hf : Measurable f) (hg : Measurable g)
    (pos : 0 < Fintype.card V)
    (uniform : ∀ v, μ.real (cell f v) = 1/(Fintype.card V : ℝ)) (v : V) :
    ∑ i, couplingMatrix μ f g v i = 1 := by
  have eq : (⋃ i, cell f v ∩ cell g i) = cell f v := by
    ext x
    constructor
    · intro h
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp h
      exact hi.1
    · intro h
      exact Set.mem_iUnion.mpr ⟨g x,h,rfl⟩
  have hd : Pairwise (Disjoint on fun i => cell f v ∩ cell g i) := by
    intro i j hij
    exact (disjoint_cells g hij).mono inter_subset_right inter_subset_right
  have hs := measureReal_iUnion_fintype (μ := μ) hd
    (fun i => (hf (measurableSet_singleton v)).inter (hg (measurableSet_singleton i)))
  rw [eq,uniform v] at hs
  have pn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast pos.ne'
  unfold couplingMatrix
  rw [← Finset.mul_sum, ← hs]
  exact mul_one_div_cancel pn

theorem coupling_mass (f : X → V) (g : X → I) (hf : Measurable f) (hg : Measurable g)
    (pos : 0 < Fintype.card V) (i : I) :
    meanCount (couplingMatrix μ f g) i/(Fintype.card V : ℝ) = μ.real (cell g i) := by
  have eq : (⋃ v, cell f v ∩ cell g i) = cell g i := by
    ext x
    constructor
    · intro h
      obtain ⟨v,hv⟩ := Set.mem_iUnion.mp h
      exact hv.2
    · intro h
      exact Set.mem_iUnion.mpr ⟨f x,rfl,h⟩
  have hd : Pairwise (Disjoint on fun v => cell f v ∩ cell g i) := by
    intro v w hvw
    exact (disjoint_cells f hvw).mono inter_subset_left inter_subset_left
  have hs := measureReal_iUnion_fintype (μ := μ) hd
    (fun v => (hf (measurableSet_singleton v)).inter (hg (measurableSet_singleton i)))
  rw [eq] at hs
  have pn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast pos.ne'
  unfold couplingMatrix meanCount
  rw [← Finset.mul_sum, ← hs]
  field_simp

theorem coupling_entry_bounds (f : X → V) (g : X → I) (hf : Measurable f) (hg : Measurable g)
    (pos : 0 < Fintype.card V)
    (uniform : ∀ v, μ.real (cell f v) = 1/(Fintype.card V : ℝ)) (v : V) (i : I) :
    0 ≤ couplingMatrix μ f g v i ∧ couplingMatrix μ f g v i ≤ 1 := by
  have nonneg (j : I) : 0 ≤ couplingMatrix μ f g v j :=
    mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg
  refine ⟨nonneg i,?_⟩
  rw [← coupling_row μ f g hf hg pos uniform v]
  classical
  exact Finset.single_le_sum (fun j _ => nonneg j) (Finset.mem_univ i)

#print axioms coupling_row
#print axioms coupling_mass
#print axioms coupling_entry_bounds
end SparseHalfGraphon
