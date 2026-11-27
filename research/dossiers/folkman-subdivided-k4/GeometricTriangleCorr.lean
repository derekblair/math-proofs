import GeometricDisjointOverlap

namespace RobustFolkman.GeometricGap
open MeasureTheory Finset Set
variable {V E : Type*} [DecidableEq V] [Fintype V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem rooted_triangle_labels (s : Finset V) (sc : s.card=3) (z : V) (zs : z∈s) :
    ∃ x y : V, x≠y ∧ z≠x ∧ z≠y ∧ s={z,x,y} := by
  have h : (s.erase z).card=2 := by rw [Finset.card_erase_of_mem zs,sc]
  obtain ⟨x,y,xy,eq⟩ := Finset.card_eq_two.mp h
  have xr : x∈s.erase z := eq.symm ▸ (by simp : x∈({x,y}:Finset V))
  have yr : y∈s.erase z := eq.symm ▸ (by simp : y∈({x,y}:Finset V))
  refine ⟨x,y,xy,(Finset.mem_erase.mp xr).1.symm,(Finset.mem_erase.mp yr).1.symm,?_⟩
  have v := Finset.insert_erase zs
  rw [eq] at v
  exact v.symm

theorem one_root_triangle_moments (t : ℝ) (s r : Finset V)
    (sc : s.card=3) (rc : r.card=3) (inter : (r∩s).card=1) :
    Moment.mean (sphericalHostWeight (E:=E) t)
      (fun g => triangleIndicator g s * triangleIndicator g r) =
      ((patternMass (E:=E) triangleCon t).toReal)^2 := by
  obtain ⟨z,zi⟩ := Finset.card_eq_one.mp inter
  have zz : z∈r∩s := zi.symm ▸ (by simp : z∈({z}:Finset V))
  obtain ⟨x,y,xy,zx,zy,ss⟩ := rooted_triangle_labels s sc z (Finset.mem_inter.mp zz).2
  obtain ⟨u,v,uv,zu,zv,rr⟩ := rooted_triangle_labels r rc z (Finset.mem_inter.mp zz).1
  have cross (a : V) (ar : a∈r) (as : a∈s) : a=z := by
    have az : a∈({z}:Finset V) := zi ▸ Finset.mem_inter.mpr ⟨ar,as⟩
    exact Finset.mem_singleton.mp az
  have xu : u≠x := fun e => zu (cross u (rr.symm ▸ by simp) (ss.symm ▸ by simp [e])).symm
  have yu : u≠y := fun e => zu (cross u (rr.symm ▸ by simp) (ss.symm ▸ by simp [e])).symm
  have xv : v≠x := fun e => zv (cross v (rr.symm ▸ by simp) (ss.symm ▸ by simp [e])).symm
  have yv : v≠y := fun e => zv (cross v (rr.symm ▸ by simp) (ss.symm ▸ by simp [e])).symm
  let R : Tuple5 V := (u,v,x,y,z)
  have ok : goodTuple (Finset.univ : EdgeGraph V) R :=
    ⟨uv,xy,zx,zy,xu,yu,xv,yv,zu.symm,zv.symm,subset_univ _⟩
  rw [ss,rr]
  exact root_overlap_explicit t R (tupleLabel_injective _ _ ok)

/-- Distinct three-sets not sharing an edge have exact independence at
the level of whole triangles (disjoint or one shared vertex). -/
theorem nonedge_overlap_triangle_moments (t : ℝ) (s r : Finset V)
    (sc : s.card=3) (rc : r.card=3) (ne : s≠r) (inter : (r∩s).card≠2) :
    Moment.mean (sphericalHostWeight (E:=E) t)
      (fun g => triangleIndicator g s * triangleIndicator g r) =
      ((patternMass (E:=E) triangleCon t).toReal)^2 := by
  have sz : (r∩s).card≤3 := (Finset.card_le_card Finset.inter_subset_left).trans_eq rc
  have nz : (r∩s).card≠3 := by
    intro h
    have ei : r∩s=r := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have er : r ⊆ s := Finset.inter_eq_left.mp ei
    exact ne (Finset.eq_of_subset_of_card_le er (by omega)).symm
  by_cases z : (r∩s).card=0
  · have dis : Disjoint s r := Finset.disjoint_iff_inter_eq_empty.mpr
      (Finset.inter_comm r s ▸ Finset.card_eq_zero.mp z)
    exact disjoint_triangle_moments t s r sc rc dis
  · exact one_root_triangle_moments t s r sc rc (by omega)

#print axioms nonedge_overlap_triangle_moments
end RobustFolkman.GeometricGap
