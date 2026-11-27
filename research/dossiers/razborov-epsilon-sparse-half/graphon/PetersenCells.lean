import PetersenStep
import StepLabels

open Set MeasureTheory SparseHalfGraphon
open scoped ENNReal
namespace SparseHalfCountableEndpoint
open PetersenParity
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

def pattern (i : Fin 4) : Bool×Bool×Bool := (bit i 0,bit i 1,bit i 2)

theorem pattern_inj : Function.Injective pattern := by
  change ∀ i j : Fin 4, pattern i=pattern j → i=j
  decide

theorem pattern_even : ∀ i : Fin 4, xor (xor (bit i 0) (bit i 1)) (bit i 2)=false := by decide

theorem sideLabel_inj : ∀ i j : Fin 10, 4 ≤ i.val → 4 ≤ j.val → sideLabel i=sideLabel j → i=j := by decide

theorem pattern_member (S : Fin 3→Set X) (i : Fin 4) {x : X}
    (hx : x∈tripleCell (S 0) (S 1) (S 2) (pattern i)) (j : Fin 3) :
    x∈side (S j) (bit i j) := by
  fin_cases j
  · exact hx.1.1
  · exact hx.1.2
  · exact hx.2

def petersenCells (A : Set X) (S : Fin 3→Set X) (P : Fin 3→Bool→Set X) (i : Fin 10) : Set X :=
  if hi : i.val<4 then A∩tripleCell (S 0) (S 1) (S 2) (pattern ⟨i.val,hi⟩)
  else P (sideLabel i).1 (sideLabel i).2

private theorem petersen_cells (A : Set X) (S : Fin 3→Set X) (P : Fin 3→Bool→Set X)
    (hA : MeasurableSet A) (hS : ∀ i, MeasurableSet (S i)) (hP : ∀ i b, MeasurableSet (P i b))
    (hp : Pairwise fun i j : Fin 3×Bool => Disjoint (P i.1 i.2) (P j.1 j.2))
    (ap : ∀ i b,Disjoint A (P i b)) : Cells (petersenCells A S P) := by
  constructor
  · intro i
    unfold petersenCells
    split
    · exact hA.inter (tripleCell_meas _ _ _ (hS 0) (hS 1) (hS 2) _)
    · exact hP _ _
  · intro i j ne
    unfold petersenCells
    split <;> rename_i hi <;> split <;> rename_i hj
    · apply (tripleCell_disjoint _ _ _ _).mono inter_subset_right inter_subset_right
      intro h
      apply ne
      exact Fin.ext (congrArg (fun k : Fin 4 => k.val) (pattern_inj h))
    · exact (ap _ _).mono_left inter_subset_left
    · exact (ap _ _).symm.mono_right inter_subset_left
    · exact hp (fun hh => ne (sideLabel_inj i j (le_of_not_gt hi) (le_of_not_gt hj) hh))

private theorem rect_sub {R S T U : Set X} (h : R⊆T) (g : S⊆U) :
    (μ.restrict R).prod (μ.restrict S) ≤ (μ.restrict T).prod (μ.restrict U) := by
  rw [Measure.prod_restrict,Measure.prod_restrict]
  exact Measure.restrict_mono_set _ (Set.prod_mono h g)

private theorem rect_rev (K : Kernel X) (R S : Set X)
    (h : ∀ᵐ z ∂(μ.restrict R).prod (μ.restrict S),K.W z=0) :
    ∀ᵐ z ∂(μ.restrict S).prod (μ.restrict R),K.W z=0 := by
  have t := (Measure.measurePreserving_swap (μ:=μ.restrict S) (ν:=μ.restrict R)).quasiMeasurePreserving.ae h
  filter_upwards [t] with ⟨x,y⟩ hz
  change K.W (y,x)=0 at hz
  rwa [K.symm y x] at hz

private theorem full_bank_cover {I : Type*} [Fintype I] (D : I→Set X) (B : Cells D)
    (mass : (∑ i,μ.real (D i))=μ.real univ) :
    ∀ᵐ x∂μ,∃ i,x∈D i := by
  have h := measureReal_iUnion_fintype (μ:=μ) B.disjoint B.meas
  have c := measureReal_add_measureReal_compl (μ:=μ) (MeasurableSet.iUnion B.meas)
  rw [h,mass] at c
  have nz : μ.real (⋃ i,D i)ᶜ = 0 := by linarith
  have ev : ∀ᵐ x∂μ,x∈⋃ i,D i := by
    apply (ae_iff).2
    change μ (⋃ i,D i)ᶜ=0
    change (μ (⋃ i,D i)ᶜ).toReal=0 at nz
    rw [ENNReal.toReal_eq_zero_iff] at nz
    exact nz.resolve_right (measure_ne_top _ _)
  exact ev.mono (fun _ => mem_iUnion.mp)

private theorem anchor_to_side_zero (K : Kernel X) (A : Set X) (S : Fin 3→Set X) (P : Set X)
    (hA : MeasurableSet A) (hS : ∀ i, MeasurableSet (S i)) (hP : MeasurableSet P)
    (i : Fin 4) (j : Fin 3) (b : Bool) (neq : bit i j≠b)
    (h : ∀ᵐ z ∂(μ.restrict A).prod (μ.restrict P),
      K.W z=(side (S j) b).indicator (fun _ => (1:ℝ)) z.1) :
    ∀ᵐ z ∂(μ.restrict (A∩tripleCell (S 0) (S 1) (S 2) (pattern i))).prod (μ.restrict P),
      K.W z=0 := by
  let D := A∩tripleCell (S 0) (S 1) (S 2) (pattern i)
  have mem : ∀ᵐ z ∂(μ.restrict D).prod (μ.restrict P), z∈D ×ˢ P := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem ((hA.inter (tripleCell_meas _ _ _ (hS 0) (hS 1) (hS 2) _)).prod hP)
  filter_upwards [mem, ae_mono (rect_sub μ (R:=D) inter_subset_left Subset.rfl) h] with z hz he
  have notside : z.1∉side (S j) b := fun m =>
    Set.disjoint_left.mp (side_disjoint _ neq) (pattern_member S i hz.1.2 j) m
  rw [he,indicator_of_notMem notside]

/-- Full even-parity Petersen geometry from the saturated rectangle model. -/
theorem petersen_even_kernel (K : Kernel X) (A : Set X) (hA : MeasurableSet A)
    (P : Fin 3→Bool→Set X) (S : Fin 3→Set X)
    (hP : ∀ i b, MeasurableSet (P i b)) (hS : ∀ i, MeasurableSet (S i))
    (hD : Pairwise fun i j : Fin 3×Bool => Disjoint (P i.1 i.2) (P j.1 j.2))
    (hOut : ∀ i b, Disjoint A (P i b))
    (hM : ∀ i b, μ.real (P i b)=1/10)
    (anchor : ∀ᵐ z ∂(μ.restrict A).prod (μ.restrict A), K.W z=0)
    (outside : ∀ i j b c, (i=j → b=c) →
      ∀ᵐ z ∂(μ.restrict (P i b)).prod (μ.restrict (P j c)), K.W z=0)
    (cross : ∀ i b, ∀ᵐ z ∂(μ.restrict A).prod (μ.restrict (P i b)),
      K.W z=(side (S i) b).indicator (fun _ => (1:ℝ)) z.1)
    (prob : μ.real univ=1)
    (par : ∀ i : Fin 4, μ.real (A∩tripleCell (S 0) (S 1) (S 2) (pattern i))=1/10) :
    (∃ H : Half μ, halfEnergy μ K H<1/50) ∨
      (∃ g : X→Fin 10, Measurable g ∧ (∀ i,μ.real (cell g i)=1/10) ∧
        K.W =ᵐ[μ.prod μ] (fun z => edgeReal (adjacent (g z.1) (g z.2)))) := by
  let D := petersenCells A S P
  let B := petersen_cells A S P hA hS hP hD hOut
  have m (i : Fin 10) : μ.real (D i)=1/10 := by
    unfold D petersenCells
    split
    · exact par _
    · exact hM _ _
  have cover := full_bank_cover μ D B (by simp only [m]; norm_num [prob,nsmul_eq_mul])
  have zeros (i j : Fin 10) (e : adjacent i j=false) :
      ∀ᵐ z ∂(μ.restrict (D i)).prod (μ.restrict (D j)),K.W z=0 := by
    unfold D petersenCells
    unfold adjacent at e
    split at e <;> rename_i hi <;> split at e <;> rename_i hj
    · rw [dite_eq_left hi,dite_eq_left hj]
      exact ae_mono (rect_sub μ inter_subset_left inter_subset_left) anchor
    · rw [dite_eq_left hi,dite_eq_right hj]
      have neq : bit ⟨i.val,hi⟩ (sideLabel j).1 ≠ (sideLabel j).2 := by
        intro k
        simp [k] at e
      exact anchor_to_side_zero μ K A S _ hA hS (hP _ _) _ _ _ neq (cross _ _)
    · rw [dite_eq_right hi,dite_eq_left hj]
      have neq : bit ⟨j.val,hj⟩ (sideLabel i).1 ≠ (sideLabel i).2 := by
        intro k
        simp [k] at e
      exact rect_rev μ K _ _ (anchor_to_side_zero μ K A S _ hA hS (hP _ _) _ _ _ neq (cross _ _))
    · rw [dite_eq_right hi,dite_eq_right hj]
      apply outside
      intro k
      by_contra b
      simp [k,b] at e
  rcases petersen_step_rigidity μ K D B cover m zeros with strict | eq
  · exact Or.inl strict
  · right
    obtain ⟨g,gm,gmass,ge⟩ := binary_label_of_step D μ adjacent B petersen_sym K cover eq
    exact ⟨g,gm,fun i => (gmass i).trans (m i),ge⟩

#print axioms petersen_even_kernel
end SparseHalfCountableEndpoint
