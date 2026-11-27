import SaturatedActivePairs

open Set MeasureTheory Function Filter
namespace SparseHalfGraphon

variable {X I : Type*} [MeasurableSpace X]
variable (ω : Measure X) [IsFiniteMeasure ω]

/-- Each side has outside neighbors only in its own partner cell, a.e.
In particular the side is independent for the outside kernel. -/
theorem paired_positive_row_confined
    (K : Kernel X) (P Q : I→Set X)
    (mp : ∀ i, MeasurableSet (P i)) (mq : ∀ i, MeasurableSet (Q i))
    (inner : ∀ i, Disjoint (P i) (Q i))
    (outer : Pairwise (Disjoint on fun i => P i∪Q i))
    (edge : ∀ᵐ z ∂ω.prod ω, 0<K.W z → ∃ i,
      (z.1∈P i ∧ z.2∈Q i) ∨ (z.1∈Q i ∧ z.2∈P i)) (i : I) :
    (∀ᵐ x ∂ω.restrict (P i), ∀ᵐ y ∂ω, 0<K.W (x,y) → y∈Q i) ∧
    (∀ᵐ x ∂ω.restrict (Q i), ∀ᵐ y ∂ω, 0<K.W (x,y) → y∈P i) := by
  have base := Measure.ae_ae_of_ae_prod edge
  have dir (x y : X) (hx : x∈P i)
      (h : ∃ j, (x∈P j ∧ y∈Q j) ∨ (x∈Q j ∧ y∈P j)) : y∈Q i := by
    obtain ⟨j,hj⟩ := h
    have hU : x∈P j∪Q j := hj.elim (fun a=>Or.inl a.1) (fun a=>Or.inr a.1)
    have e : i=j := by
      by_contra ne
      exact Set.disjoint_left.mp (outer ne) (Or.inl hx) hU
    subst j
    exact hj.elim (fun a=>a.2) (fun a=>False.elim (Set.disjoint_left.mp (inner i) hx a.1))
  constructor
  · filter_upwards [base.filter_mono (Measure.restrict_le_self (s:=P i)).absolutelyContinuous.ae_le,
      ae_restrict_mem (μ:=ω) (mp i)] with x hx hP
    filter_upwards [hx] with y row positive
    exact dir x y hP (row positive)
  · filter_upwards [base.filter_mono (Measure.restrict_le_self (s:=Q i)).absolutelyContinuous.ae_le,
      ae_restrict_mem (μ:=ω) (mq i)] with x hx hQ
    filter_upwards [hx] with y row positive
    obtain ⟨j,hj⟩ := row positive
    have hU : x∈P j∪Q j := hj.elim (fun a=>Or.inl a.1) (fun a=>Or.inr a.1)
    have e : i=j := by
      by_contra ne
      exact Set.disjoint_left.mp (outer ne) (Or.inr hQ) hU
    subst j
    exact hj.elim (fun a=>False.elim (Set.disjoint_left.mp (inner i) a.1 hQ)) (fun a=>a.2)

/-- Under confinement, the partner-restricted degree equals the total degree. -/
theorem deg_restrict_of_row_confined (K : Kernel X) (S T : Set X) (mt : MeasurableSet T)
    (h : ∀ᵐ x ∂ω.restrict S, ∀ᵐ y ∂ω, 0<K.W (x,y) → y∈T) :
    ∀ᵐ x ∂ω.restrict S, deg (ω.restrict T) K x=deg ω K x := by
  classical
  filter_upwards [h] with x hx
  change (∫ y in T,K.W (x,y) ∂ω)=_
  rw [←integral_indicator mt]
  apply integral_congr_ae
  filter_upwards [hx] with y h
  by_cases yT : y∈T
  · rw [indicator_of_mem yT]
  · rw [indicator_of_notMem yT]
    exact le_antisymm (K.nonneg _) (le_of_not_gt (fun a=>yT (h a)))

#print axioms paired_positive_row_confined
#print axioms deg_restrict_of_row_confined
/-- A retained pair with positive left mass actually carries positive
edge integral; it is not merely a pair of nonnull profile labels. -/
theorem paired_active_positive_edge_mass
    (K : Kernel X) (P Q : I→Set X)
    (mp : ∀ i, MeasurableSet (P i)) (mq : ∀ i, MeasurableSet (Q i))
    (inner : ∀ i, Disjoint (P i) (Q i))
    (outer : Pairwise (Disjoint on fun i => P i∪Q i))
    (edge : ∀ᵐ z ∂ω.prod ω, 0<K.W z → ∃ i,
      (z.1∈P i ∧ z.2∈Q i) ∨ (z.1∈Q i ∧ z.2∈P i))
    (active : ∀ᵐ x ∂ω, x∈(⋃ i,P i∪Q i) ↔ 0<deg ω K x)
    (i : I) (positive : 0<ω.real (P i)) :
    0 < ∫ x in P i, deg (ω.restrict (Q i)) K x ∂ω := by
  have c := (paired_positive_row_confined ω K P Q mp mq inner outer edge i).1
  have d := deg_restrict_of_row_confined ω K (P i) (Q i) (mq i) c
  have e : ∀ᵐ x ∂ω.restrict (P i), 0<deg (ω.restrict (Q i)) K x := by
    filter_upwards [d,active.filter_mono (Measure.restrict_le_self (s:=P i)).absolutelyContinuous.ae_le,
      ae_restrict_mem (μ:=ω) (mp i)] with x hx ax px
    rw [hx]
    exact ax.mp (mem_iUnion.mpr ⟨i,Or.inl px⟩)
  have norm : Integrable (deg (ω.restrict (Q i)) K) (ω.restrict (P i)) :=
    integrable_bounded _ (deg_measurable _ K) (deg_nonneg _ K) (deg_le_mass _ K)
  by_contra! H
  have E := (integral_eq_zero_iff_of_nonneg (deg_nonneg _ K) norm).mp
    (le_antisymm H (integral_nonneg (deg_nonneg _ K)))
  have bad : ∀ᵐ _ : X ∂ω.restrict (P i), False := by
    filter_upwards [e,E] with x hx eq
    exact (ne_of_gt hx) eq
  have hz : (ω.restrict (P i)) univ=0 := by
    simpa only [ae_iff, not_false_eq_true, Set.setOf_true] using bad
  rw [Measure.restrict_apply_univ] at hz
  simp [measureReal_def,hz] at positive

#print axioms paired_active_positive_edge_mass
end SparseHalfGraphon
