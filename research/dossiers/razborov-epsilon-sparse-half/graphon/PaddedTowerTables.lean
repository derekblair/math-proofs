import PaddedRegularityTower
import FiberIntegrals
import TableConsistency
open MeasureTheory Set Function
open scoped BigOperators

namespace SparseHalfGraphon

variable {Y : Type*} [MeasurableSpace Y]

/-- Splitting a cell integral works for the original kernel itself, not
merely for a function already constant on the fine cells. -/
theorem integral_cell_refines (ν : Measure Y) {I J : Type*}
    [DecidableEq I] [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (c : Y → I) (d : Y → J) (p : J → I)
    (hd : Measurable d) (hp : ∀ y, c y = p (d y))
    (f : Y → ℝ) (hf : Integrable f ν) (i : I) :
    (∫ y in cell c i, f y ∂ν) =
      ∑ j with p j = i, ∫ y in cell d j, f y ∂ν := by
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
  rw [integral_iUnion_fintype hm hD (fun _ => hf.integrableOn)]
  exact (Finset.sum_subtype (p := fun j => p j = i)
    (Finset.univ.filter (fun j => p j = i)) (fun _ => by simp)
    (fun j => ∫ y in cell d j, f y ∂ν)).symm

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

private lemma mass_cell_total {I : Type*} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (c : X → I) (hc : Measurable c) :
    ∑ i, μ.real (cell c i) = mass μ := by
  have h := integral_cell_refines μ (fun _ : X => ()) c (fun _ : I => ())
    hc (fun _ => rfl) (fun _ => (1 : ℝ)) (integrable_const 1) ()
  simpa [cell,setIntegral_const,smul_eq_mul,mass] using h.symm

variable {d : ℕ → ℕ}

noncomputable def towerTables (K : Kernel X) (hμ : mass μ = 1)
    (A : PaddedTower (X := X) d) :
    CoherentTables (fun n => Fin (d n)) A.parent where
  cell n i := μ.real (cell (A.label n) i)
  joint n i j := ∫ z in cell (pairLabel (A.label n)) (i,j), K.W z ∂μ.prod μ
  cell_zero _ _ := measureReal_nonneg
  cell_total n := (mass_cell_total μ _ (A.measurable_label n)).trans hμ
  cell_split n i := by
    have h := integral_cell_refines μ (A.label n) (A.label (n+1)) (A.parent n)
      (A.measurable_label (n+1)) (A.parent_exact n) (fun _ => (1 : ℝ))
      (integrable_const 1) i
    simpa [setIntegral_const,smul_eq_mul] using h
  joint_zero _ _ _ := integral_nonneg K.nonneg
  joint_bound n i j := by
    have h := integral_mono
      (integrable_bounded (μ.prod μ) K.measurable_W K.nonneg K.le_one).integrableOn
      (integrable_const (μ := (μ.prod μ).restrict (cell (pairLabel (A.label n)) (i,j))) (1:ℝ))
      K.le_one
    simpa [pair_cell,setIntegral_const,smul_eq_mul,measureReal_prod_prod] using h
  joint_symm n i j := by
    simp only [pair_cell]
    have h := setIntegral_prod_swap (μ:=μ) (ν:=μ) K.W
      (s:=cell (A.label n) i) (t:=cell (A.label n) j)
    have E : (fun z : X × X => K.W z.swap) = K.W := funext (fun z => K.symm z.2 z.1)
    rw [E] at h
    exact h.symm
  joint_split n i j := by
    let pp (z : Fin (d (n+1)) × Fin (d (n+1))) :=
      (A.parent n z.1,A.parent n z.2)
    have E (z : X × X) : pairLabel (A.label n) z = pp (pairLabel (A.label (n+1)) z) :=
      Prod.ext (A.parent_exact n z.1) (A.parent_exact n z.2)
    have h := integral_cell_refines (μ.prod μ) (pairLabel (A.label n))
      (pairLabel (A.label (n+1))) pp
      (pair_label_meas _ (A.measurable_label (n+1))) E K.W
      (integrable_bounded (μ.prod μ) K.measurable_W K.nonneg K.le_one) (i,j)
    let f (z : Fin (d (n+1)) × Fin (d (n+1))) :=
      ∫ y in cell (pairLabel (A.label (n+1))) z, K.W y ∂μ.prod μ
    change _ = ∑ z with pp z = (i,j), f z at h
    change _ = ∑ a with A.parent n a = i, ∑ b with A.parent n b = j, f (a,b)
    rw [h]
    have hsets : Finset.univ.filter (fun z => pp z = (i,j)) =
        (Finset.univ.filter (fun a => A.parent n a = i)).product
        (Finset.univ.filter (fun b => A.parent n b = j)) := by
      apply Finset.ext
      intro z
      simp [pp,Prod.ext_iff]
    rw [hsets]
    exact Finset.sum_product ..

/-- The coherent table's normalized rectangle entry is precisely the
block-kernel value, including zero-mass rectangles by totalized division. -/
theorem tower_table_block (K : Kernel X) (hμ : mass μ = 1)
    (A : PaddedTower (X := X) d) (n : ℕ) (x y : X) :
    (blockKernel μ K (A.label n) (A.measurable_label n)).W (x,y) =
      (towerTables μ K hμ A).joint n (A.label n x) (A.label n y) /
      ((towerTables μ K hμ A).cell n (A.label n x) *
       (towerTables μ K hμ A).cell n (A.label n y)) := by
  change meanCell (μ.prod μ) (pairLabel (A.label n)) K.W (A.label n x,A.label n y) = _
  unfold meanCell
  change _ / (μ.prod μ).real (cell (pairLabel (A.label n)) (A.label n x,A.label n y)) =
    _ / (μ.real (cell (A.label n) (A.label n x)) * μ.real (cell (A.label n) (A.label n y)))
  rw [pair_cell,measureReal_prod_prod]
  simp [towerTables,pair_cell]

#print axioms tower_table_block
#print axioms towerTables
end SparseHalfGraphon
