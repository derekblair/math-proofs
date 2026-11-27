import MeasureSignatures

open Set MeasureTheory
namespace SparseHalfCountableEndpoint

variable {X : Type*} [MeasurableSpace X]
variable (ν : Measure X) [IsFiniteMeasure ν]

/-- Generic finite disjoint-cell allocation, usable for both the four
two-signature cells and the eight three-signature cells. Cost is exact
for any real root load constant on each cell. -/
theorem measurable_cell_fill {J : Type*} [Fintype J]
    (S : J→Set X) (hS : ∀ j, MeasurableSet (S j))
    (hd : Pairwise fun j k => Disjoint (S j) (S k))
    (q c : J→ℝ) (hq : ∀ j, 0≤q j ∧ q j≤ν.real (S j))
    (load : X→ℝ) (hl : ∀ j x, x∈S j → load x=c j) :
    ∃ f : X→ℝ, Measurable f ∧ (∀ x,0≤f x ∧ f x≤1) ∧
      (∫ x,f x ∂ν)=∑ j,q j ∧
      (∫ x,load x*f x ∂ν)=∑ j,c j*q j := by
  classical
  let g := fun j => SparseHalfGraphon.allocSet ν (S j) (q j)
  have gm j := SparseHalfGraphon.allocSet_bmeas ν (S j) (hS j) (q j) (hq j).1 (hq j).2
  have gi j := SparseHalfGraphon.bMeas_integrable ν (gm j)
  have gn (j : J) (x : X) := SparseHalfGraphon.allocSet_nn ν (S j) (q j) (hq j).1 x
  have gu (j : J) (x : X) := SparseHalfGraphon.allocSet_le ν (S j) (q j) (hq j).2 x
  let f := fun x => ∑ j, g j x
  have H (x : X) : 0≤f x ∧ f x≤1 := by
    refine ⟨Finset.sum_nonneg fun j _ => gn j x,?_⟩
    by_cases hx : ∃ j, x∈S j
    · obtain ⟨j,hj⟩ := hx
      have e : f x=g j x := by
        unfold f
        apply Finset.sum_eq_single j
        · intro k _ kn
          exact SparseHalfGraphon.allocSet_support ν (S k) (q k)
            (fun hk => Set.disjoint_left.mp (hd kn) hk hj)
        · simp
      exact e.trans_le (gu j x)
    · have e : f x=0 := Finset.sum_eq_zero fun j _ =>
        SparseHalfGraphon.allocSet_support ν (S j) (q j) (fun h => hx ⟨j,h⟩)
      simp [e]
  have fM : Measurable f := by
    apply Finset.measurable_sum
    intro j _
    exact (gm j).1
  have intMass j : (∫ x,g j x ∂ν)=q j :=
    SparseHalfGraphon.allocSet_mass ν (S j) (hS j) (q j) (hq j).1 (hq j).2
  have point (j : J) (x : X) : load x*g j x=c j*g j x := by
    by_cases hx : x∈S j
    · rw [hl j x hx]
    · change load x*SparseHalfGraphon.allocSet _ _ _ _=c j*SparseHalfGraphon.allocSet _ _ _ _
      rw [SparseHalfGraphon.allocSet_support ν (S j) (q j) hx,mul_zero,mul_zero]
  have integral_cost (j : J) : (∫ x,c j*g j x ∂ν)=c j*q j := by
    rw [integral_const_mul,intMass]
  refine ⟨f,fM,H,?_,?_⟩
  · unfold f
    rw [integral_finsetSum _ (fun j _ => gi j)]
    exact Finset.sum_congr rfl (fun j _ => intMass j)
  · unfold f
    simp only [Finset.mul_sum,point]
    rw [integral_finsetSum _ (fun j _ => (gi j).const_mul (c j))]
    exact Finset.sum_congr rfl (fun j _ => integral_cost j)

/-- Either the original alignment or the second flipped profile contains
a zero-incidence cell of capacity at least one. -/
theorem favorable_flip (S T : Set X) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hV : ν.real univ=4) (hS' : ν.real S=2) (hT' : ν.real T=2) :
    1≤ν.real (sigCell S T (false,false)) ∨
    1≤ν.real (sigCell S Tᶜ (false,false)) := by
  obtain ⟨_,_,_,_,h⟩ := four_cell_mass ν S T hS hT hV hS' hT'
  change ν.real (Sᶜ∩T)=2-ν.real (Sᶜ∩Tᶜ) at h
  change 1≤ν.real (Sᶜ∩Tᶜ) ∨ 1≤ν.real (Sᶜ∩(Tᶜ)ᶜ)
  rw [compl_compl,h]
  rcases le_total 1 (ν.real (Sᶜ∩Tᶜ)) with h | h
  · exact Or.inl h
  · right; linarith

/-- Measurable realization of the numeric four-cell allocation. The
outside-side masses l,r enter as binary cross-loads on the A anchor. -/
theorem realize_four_cells (S T : Set X) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hV : ν.real univ=4) (hS' : ν.real S=2) (hT' : ν.real T=2)
    (b l r C : ℝ)
    (F : FourCellFill (ν.real (sigCell S T (false,false))) b l r C) :
    ∃ f : X→ℝ, Measurable f ∧ (∀ x,0≤f x ∧ f x≤1) ∧
      (∫ x,f x ∂ν)=b ∧
      (∫ x, (S.indicator (fun _ => l) x+T.indicator (fun _ => r) x)*f x ∂ν)≤C := by
  classical
  let x := ν.real (sigCell S T (false,false))
  obtain ⟨_,_,m33,m11,m22⟩ := four_cell_mass ν S T hS hT hV hS' hT'
  obtain ⟨u,v,w,z,un,uc,vn,vc,wn,wc,zn,zc,mb,cc⟩ := F
  let mass : Bool×Bool→ℝ
    | (false,false) => u
    | (true,false) => v
    | (false,true) => w
    | (true,true) => z
  let loads : Bool×Bool→ℝ := fun j => (if j.1 then l else 0)+(if j.2 then r else 0)
  have caps (j : Bool×Bool) : 0≤mass j ∧ mass j≤ν.real (sigCell S T j) := by
    rcases j with ⟨a,b⟩
    cases a <;> cases b
    · exact ⟨un,uc⟩
    · exact ⟨wn,m22.symm ▸ wc⟩
    · exact ⟨vn,m11.symm ▸ vc⟩
    · exact ⟨zn,m33.symm ▸ zc⟩
  have on_cell (j : Bool×Bool) (y : X) (h : y∈sigCell S T j) :
      S.indicator (fun _ => l) y+T.indicator (fun _ => r) y=loads j := by
    rcases j with ⟨a,b⟩
    cases a <;> cases b
    · change y∉S ∧ y∉T at h
      simp [loads,indicator_of_notMem h.1,indicator_of_notMem h.2]
    · change y∉S ∧ y∈T at h
      simp [loads,indicator_of_notMem h.1,indicator_of_mem h.2]
    · change y∈S ∧ y∉T at h
      simp [loads,indicator_of_mem h.1,indicator_of_notMem h.2]
    · change y∈S ∧ y∈T at h
      simp [loads,indicator_of_mem h.1,indicator_of_mem h.2] 
  obtain ⟨f,fm,fx,hm,hl⟩ :=
    measurable_cell_fill ν (sigCell S T) (sigCell_meas S T hS hT) (fun _ _ => sigCell_disjoint S T)
      mass loads caps (fun y => S.indicator (fun _ => l) y+T.indicator (fun _ => r) y) on_cell
  refine ⟨f,fm,fx,?_,?_⟩
  · rw [hm,Fintype.sum_prod_type]
    simp only [Fintype.sum_bool,mass]
    linarith
  · rw [hl,Fintype.sum_prod_type]
    simp only [Fintype.sum_bool,loads,mass,Prod.fst,Prod.snd,Bool.false_eq_true,if_false,
      if_true,zero_add,add_zero,zero_mul]
    linarith

#print axioms measurable_cell_fill
#print axioms favorable_flip
#print axioms realize_four_cells
end SparseHalfCountableEndpoint
