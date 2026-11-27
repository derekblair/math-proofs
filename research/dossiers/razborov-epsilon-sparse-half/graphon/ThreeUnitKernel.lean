import RectangleJoin
import PetersenParity

open Set MeasureTheory SparseHalfGraphon
open scoped ENNReal
namespace SparseHalfCountableEndpoint
variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

/-- The three unit pairs chamber in an actual kernel, conditional only
on the extracted saturated rectangle model, yields a strict half or
exactly the two complementary Petersen parity descriptions. -/
theorem three_unit_kernel (K : Kernel X) (A : Set X) (hA : MeasurableSet A)
    (P : Fin 3→Bool→Set X) (S : Fin 3→Set X)
    (hP : ∀ i b, MeasurableSet (P i b)) (hS : ∀ i, MeasurableSet (S i))
    (hD : ∀ i j b c, i≠j → Disjoint (P i b) (P j c))
    (hOut : ∀ i b, Disjoint A (P i b))
    (hM : ∀ i b, μ.real (P i b)=1/10)
    (anchor : ∀ᵐ z ∂(μ.restrict A).prod (μ.restrict A), K.W z=0)
    (outside : ∀ i j b c, (i=j → b=c) →
      ∀ᵐ z ∂(μ.restrict (P i b)).prod (μ.restrict (P j c)), K.W z=0)
    (cross : ∀ i b, ∀ᵐ z ∂(μ.restrict A).prod (μ.restrict (P i b)),
      K.W z=(side (S i) b).indicator (fun _ => (1:ℝ)) z.1)
    (hA4 : ((10:ℝ≥0∞) • μ.restrict A).real univ=4)
    (hS2 : ∀ i, ((10:ℝ≥0∞) • μ.restrict A).real (S i)=2) :
    (∃ H : Half μ, halfEnergy μ K H<1/50) ∨ ∃ v : Bool,
      ∀ a b c : Bool, ((10:ℝ≥0∞) • μ.restrict A).real
        (tripleCell (S 0) (S 1) (S 2) (a,b,c))=
        if xor (xor a b) c=v then (1:ℝ) else 0 := by
  let ν := (10:ℝ≥0∞) • μ.restrict A
  haveI : IsFiniteMeasure ν := by dsimp [ν]; exact (μ.restrict A).smul_finite (by norm_num)
  rcases three_unit_rigidity ν (S 0) (S 1) (S 2) (hS 0) (hS 1) (hS 2)
    hA4 (hS2 0) (hS2 1) (hS2 2) with good | par
  · left
    obtain ⟨⟨a,b,c⟩,f,hf,hfb,mf,cf⟩ := good
    let o := (![a,b,c] : Fin 3→Bool)
    let C := ∫ x, threeLoad (side (S 0) a) (side (S 1) b) (side (S 2) c) x*f x ∂ν
    have hC : C<2 := cf
    have cost : (∫ x, (∑ j : Fin 3,(side (S j) (o j)).indicator
        (fun _ => (10:ℝ)*(1/10)) x)*f x ∂ν)≤C := by
      change _ ≤ _
      apply le_of_eq
      unfold C
      apply integral_congr_ae
      filter_upwards with x
      rw [Fin.sum_univ_three]
      norm_num [threeLoad,o]
    obtain ⟨H,hH⟩ := join_rectangles μ K A hA
      (fun j => P j (o j)) (fun j => side (S j) (o j))
      (fun j => hP j (o j)) (fun i j hij => hD i j _ _ hij)
      (fun j => hOut j (o j)) (fun _=>1/10) (fun j => ⟨by norm_num,(hM j _).ge⟩)
      (fun i j => outside i j _ _ (congrArg o)) (fun j => cross j _)
      anchor f hf hfb 2 C mf (by norm_num) cost
    exact ⟨H,hH.trans_lt (by linarith)⟩
  · exact Or.inr par

#print axioms three_unit_kernel
end SparseHalfCountableEndpoint
