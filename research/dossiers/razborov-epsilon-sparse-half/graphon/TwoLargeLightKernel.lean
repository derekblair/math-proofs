import RigidityTransferLabels
import RectangleJoin

open Set MeasureTheory SparseHalfGraphon
open scoped ENNReal
namespace SparseHalfCountableEndpoint
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- The zero-heavy price-two endpoint with two (2,1) blocks is strictly
below target. Align the two large sides when their joint free cell has
mass ≥1; otherwise cross one large and one small and fill the cheaper
single-incidence cell. The proof uses the actual measurable kernel. -/
theorem two_large_light_strict (K : Kernel X) (A : Set X) (hA : MeasurableSet A)
    (P : Fin 2→Bool→Set X) (S : Fin 2→Set X)
    (hP : ∀ i b, MeasurableSet (P i b)) (hS : ∀ i, MeasurableSet (S i))
    (hD : ∀ i j b c, i≠j → Disjoint (P i b) (P j c))
    (hOut : ∀ i b, Disjoint A (P i b))
    (hM : ∀ i b, μ.real (P i b)=if b then 1/5 else 1/10)
    (anchor : ∀ᵐ z ∂(μ.restrict A).prod (μ.restrict A), K.W z=0)
    (outside : ∀ i j b c, (i=j → b=c) →
      ∀ᵐ z ∂(μ.restrict (P i b)).prod (μ.restrict (P j c)), K.W z=0)
    (cross : ∀ i b, ∀ᵐ z ∂(μ.restrict A).prod (μ.restrict (P i b)),
      K.W z=(side (S i) b).indicator (fun _ => (1:ℝ)) z.1)
    (hA4 : ((10:ℝ≥0∞) • μ.restrict A).real univ=4)
    (hS2 : ∀ i, ((10:ℝ≥0∞) • μ.restrict A).real (S i)=2) :
    ∃ H : Half μ,halfEnergy μ K H<1/50 := by
  let ν := (10:ℝ≥0∞) • μ.restrict A
  have : IsFiniteMeasure ν := by dsimp [ν]; exact (μ.restrict A).smul_finite (by norm_num)
  have total : ν.real univ=4 := hA4
  have halves (i : Fin 2) : ν.real (S i)=2 := hS2 i
  have co : ν.real (S 1)ᶜ=2 := by
    linarith [measureReal_add_measureReal_compl (μ:=ν) (hS 1),halves 1]
  have glue (c : Bool) (b C : ℝ) (clt : C<2)
      (f : X→ℝ) (fm : Measurable f) (fb : ∀ x,0≤f x ∧ f x≤1)
      (ff : (∫ x,f x ∂ν)=b)
      (mass : (1/5:ℝ)+(if c then 1/5 else 1/10)=(5-b)/10)
      (hcost : (∫ x,((S 0).indicator (fun _ => 2) x+
          (side (S 1) c).indicator (fun _ =>if c then (2:ℝ) else 1) x)*f x ∂ν)≤C) :
      ∃ H : Half μ,halfEnergy μ K H<1/50 := by
    let o : Fin 2→Bool := ![true,c]
    let q : Fin 2→ℝ := fun j => if o j then 1/5 else 1/10
    have qcaps (j : Fin 2) : 0≤q j ∧ q j≤μ.real (P j (o j)) := by
      refine ⟨?_, (hM j _).ge⟩
      unfold q
      split <;> norm_num
    have mo : (∑ j,q j)=(5-b)/10 := by
      rw [Fin.sum_univ_two]
      simpa [q,o] using mass
    have cc : (∫ x, (∑ j : Fin 2,(side (S j) (o j)).indicator (fun _ => 10*q j) x)*f x ∂ν)≤C := by
      simp only [Fin.sum_univ_two,q,o,Matrix.cons_val_zero,Matrix.cons_val_one,side_true,
        ite_eq_left rfl]
      cases c <;> norm_num at hcost ⊢ <;> exact hcost
    obtain ⟨H,h⟩ := join_rectangles μ K A hA (fun j => P j (o j)) (fun j => side (S j) (o j))
      (fun j => hP j _) (fun i j e => hD i j _ _ e) (fun j => hOut j _) q qcaps
      (fun i j => outside i j _ _ (congrArg o)) (fun j => cross j _) anchor
      f fm fb b C ff mo cc
    exact ⟨H,h.trans_lt (by linarith)⟩
  rcases favorable_flip ν (S 0) (S 1) (hS 0) (hS 1) total (halves 0) (halves 1) with
    align | crossed
  · have funn : FourCellFill (ν.real (sigCell (S 0) (S 1) (false,false))) 1 2 2 0 :=
      ⟨1,0,0,0,by norm_num,align,le_rfl,
        by linarith [(four_cell_mass ν (S 0) (S 1) (hS 0) (hS 1) total (halves 0) (halves 1)).2.1],
        le_rfl, by linarith [(four_cell_mass ν (S 0) (S 1) (hS 0) (hS 1) total (halves 0) (halves 1)).2.1],
        le_rfl, measureReal_nonneg, by norm_num, by norm_num⟩
    obtain ⟨f,fm,fb,ff,fc⟩ := realize_four_cells ν (S 0) (S 1) (hS 0) (hS 1) total
      (halves 0) (halves 1) 1 2 2 0 funn
    exact glue true 1 0 (by norm_num) f fm fb ff (by norm_num) fc
  · let x := ν.real (sigCell (S 0) (S 1)ᶜ (false,false))
    have x2 : x≤2 := (four_cell_mass ν (S 0) (S 1)ᶜ (hS 0) (hS 1).compl total (halves 0) co).2.1
    have funn : FourCellFill x 2 2 1 1 :=
      ⟨x,0,2-x,0,by linarith,le_rfl,le_rfl,by linarith,
        by linarith,le_rfl,le_rfl,by linarith,by ring, by linarith⟩
    obtain ⟨f,fm,fb,ff,fc⟩ := realize_four_cells ν (S 0) (S 1)ᶜ (hS 0) (hS 1).compl total
      (halves 0) co 2 2 1 1 funn
    exact glue false 2 1 (by norm_num) f fm fb ff (by norm_num) fc

#print axioms two_large_light_strict
end SparseHalfCountableEndpoint
