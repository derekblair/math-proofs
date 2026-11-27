import MissingRectangle

open Set MeasureTheory SparseHalfGraphon
namespace SparseHalfCountableEndpoint
variable {X : Type*} [MeasurableSpace X]
variable {I : Type*} [Fintype I]

/-- A finite measurable cell bank, whose support need not be exactly
all points (an a.e. cover suffices in the completion theorem). -/
structure Cells (P : I→Set X) : Prop where
  meas : ∀ i, MeasurableSet (P i)
  disjoint : Pairwise fun i j => Disjoint (P i) (P j)

variable (P : I→Set X) (e : I→I→Bool)

noncomputable def stepW (z : X×X) : ℝ := ∑ i : I×I,
  (P i.1 ×ˢ P i.2).indicator (fun _ => if e i.1 i.2 then 1 else 0) z

theorem stepW_on (B : Cells P) (i j : I) {x y : X} (hx : x∈P i) (hy : y∈P j) :
    stepW P e (x,y)=(if e i j then 1 else 0) := by
  classical
  unfold stepW
  rw [Finset.sum_eq_single (i,j)]
  · exact indicator_of_mem (show (x,y)∈P i ×ˢ P j from ⟨hx,hy⟩) _
  · intro a _ hne
    apply indicator_of_notMem
    intro hm
    have hi : a.1=i := by by_contra n; exact Set.disjoint_left.mp (B.disjoint n) hm.1 hx
    have hj : a.2=j := by by_contra n; exact Set.disjoint_left.mp (B.disjoint n) hm.2 hy
    exact hne (Prod.ext hi hj)
  · simp

theorem stepW_off (z : X×X) (h : ¬(∃ i, z.1∈P i) ∨ ¬(∃ j, z.2∈P j)) :
    stepW P e z=0 := by
  unfold stepW
  apply Finset.sum_eq_zero
  intro a _
  apply indicator_of_notMem
  intro hm
  exact h.elim (fun h => h ⟨a.1,hm.1⟩) (fun h => h ⟨a.2,hm.2⟩)

noncomputable def stepKernel (B : Cells P) (sym : ∀ i j,e i j=e j i) : Kernel X where
  W := stepW P e
  measurable_W := Finset.measurable_sum _ (fun a _ => measurable_const.indicator
    ((B.meas a.1).prod (B.meas a.2)))
  nonneg := by
    rintro ⟨x,y⟩
    rcases em (∃ i, x∈P i) with ⟨i,hi⟩|hx
    · rcases em (∃ j,y∈P j) with ⟨j,hj⟩|hy
      · rw [stepW_on P e B i j hi hj]; split <;> norm_num
      · rw [stepW_off P e (x,y) (Or.inr hy)]
    · rw [stepW_off P e (x,y) (Or.inl hx)]
  le_one := by
    rintro ⟨x,y⟩
    rcases em (∃ i,x∈P i) with ⟨i,hi⟩|hx
    · rcases em (∃ j,y∈P j) with ⟨j,hj⟩|hy
      · rw [stepW_on P e B i j hi hj]; split <;> norm_num
      · rw [stepW_off P e (x,y) (Or.inr hy)]; norm_num
    · rw [stepW_off P e (x,y) (Or.inl hx)]; norm_num
  symm := by
    intro x y
    rcases em (∃ i,x∈P i) with ⟨i,hi⟩|hx
    · rcases em (∃ j,y∈P j) with ⟨j,hj⟩|hy
      · rw [stepW_on P e B i j hi hj,stepW_on P e B j i hj hi,sym i j]
      · rw [stepW_off P e (x,y) (Or.inr hy),stepW_off P e (y,x) (Or.inl hy)]
    · rw [stepW_off P e (x,y) (Or.inl hx),stepW_off P e (y,x) (Or.inr hx)]

variable (μ : Measure X) [IsFiniteMeasure μ]

/-- One limited-cell allocation, with explicit formula so its positive
support is available to the missing-rectangle argument. -/
noncomputable def stepAllocation (q : I→ℝ) (x : X) : ℝ := ∑ i, allocSet μ (P i) (q i) x

lemma stepAllocation_on (B : Cells P) (q : I→ℝ) {i : I} {x : X} (hx : x∈P i) :
    stepAllocation P μ q x=q i/μ.real (P i) := by
  classical
  unfold stepAllocation
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem hx _
  · intro k _ ne
    exact allocSet_support μ (P k) (q k) (fun hk => Set.disjoint_left.mp (B.disjoint ne) hk hx)
  · simp

lemma stepAllocation_off (q : I→ℝ) {x : X} (h : ¬∃ i,x∈P i) :
    stepAllocation P μ q x=0 := by
  unfold stepAllocation
  exact Finset.sum_eq_zero fun i _ => allocSet_support μ (P i) (q i) (fun hi => h ⟨i,hi⟩)

noncomputable def stepHalf (B : Cells P) (q : I→ℝ)
    (hq : ∀ i, 0≤q i ∧ q i≤μ.real (P i)) (mass : ∑ i,q i=1/2) : Half μ where
  f := stepAllocation P μ q
  measurable_f := Finset.measurable_sum _ (fun i _ =>
    (allocSet_bmeas μ (P i) (B.meas i) (q i) (hq i).1 (hq i).2).1)
  nn := fun x => Finset.sum_nonneg (fun i _ => allocSet_nn μ (P i) (q i) (hq i).1 x)
  le_one := fun x => by
    rcases em (∃ i,x∈P i) with ⟨i,hi⟩|h
    · rw [stepAllocation_on P μ B q hi]
      by_cases z : μ.real (P i)=0
      · simp [z]
      · exact (div_le_iff₀ (lt_of_le_of_ne measureReal_nonneg (Ne.symm z))).2 (by simpa using (hq i).2)
    · rw [stepAllocation_off P μ q h]; norm_num
  mass_half := by
    unfold stepAllocation
    rw [integral_finsetSum _ (fun i _ => bMeas_integrable μ
      (allocSet_bmeas μ (P i) (B.meas i) (q i) (hq i).1 (hq i).2)),←mass]
    exact Finset.sum_congr rfl (fun i _ => allocSet_mass μ (P i) (B.meas i) (q i) (hq i).1 (hq i).2)

#print axioms stepHalf
end SparseHalfCountableEndpoint
