import TwoLargeLightKernel
import TwoHeavyProfiles

open Set MeasureTheory SparseHalfGraphon SparseHalfLowSmallSide
open scoped ENNReal
namespace SparseHalfCountableEndpoint
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

private lemma fill_flip {x b l r C : ℝ} (f : FourCellFill x b l r C) : FourCellFill x b r l C := by
  obtain ⟨a,u,v,w,an,ac,un,uc,vn,vc,wn,wc,hm,hb⟩ := f
  refine ⟨a,v,u,w,an,ac,vn,vc,un,uc,wn,wc,?_,?_⟩ <;> linarith

private lemma fill_unsort {x b l r C : ℝ} (f : FourCellFill x b (min l r) (max l r) C) :
    FourCellFill x b l r C := by
  rcases le_total l r with a|a
  · simpa only [min_eq_left a,max_eq_right a] using f
  · apply fill_flip
    simpa only [min_eq_right a,max_eq_left a] using f

/-- Actual kernel closure of the two-heavy nonpivot chamber. The light
and isolate pools need not be represented individually because the
strict orientation uses neither of them. -/
theorem two_heavy_kernel_of_scalar (K : Kernel X) (A : Set X) (hA : MeasurableSet A)
    (B : Fin 2→Bool→Set X) (S : Fin 2→Set X)
    (hB : ∀ i b,MeasurableSet (B i b)) (hS : ∀ i,MeasurableSet (S i))
    (hD : ∀ i j b c,i≠j → Disjoint (B i b) (B j c))
    (hOut : ∀ i b,Disjoint A (B i b))
    (anchor : ∀ᵐ z ∂(μ.restrict A).prod (μ.restrict A),K.W z=0)
    (outside : ∀ i j b c,(i=j→b=c) →
      ∀ᵐ z ∂(μ.restrict (B i b)).prod (μ.restrict (B j c)),K.W z=0)
    (cross : ∀ i b,∀ᵐ z ∂(μ.restrict A).prod (μ.restrict (B i b)),
      K.W z=(side (S i) b).indicator (fun _ => (1:ℝ)) z.1)
    (hA4 : ((10:ℝ≥0∞) • μ.restrict A).real univ=4)
    (hS2 : ∀ i,((10:ℝ≥0∞) • μ.restrict A).real (S i)=2)
    (h p q r s L : ℝ)
    (mB : ∀ i b, μ.real (B i b) =
      ((![if b then p else q,if b then r else s] : Fin 2→ℝ) i)/10)
    (hq : 1<q) (hs : 1<s) (hqp : q≤p) (hsr : s≤r) (hpr : p≤r) (hr2 : r≤2)
    (_hcap : h+L≤2)
    (hscalar : r*(4-max (p+s) (r+q))<2 ∨
      (h=2/3 ∧ p=3/2 ∧ r=3/2 ∧ q=7/6 ∧ s=7/6 ∧ L=0)) :
    ∃ H : Half μ,halfEnergy μ K H<1/50 := by
  let ν := (10:ℝ≥0∞) • μ.restrict A
  have : IsFiniteMeasure ν := by dsimp [ν]; exact (μ.restrict A).smul_finite (by norm_num)
  have full : ν.real univ=4 := hA4
  have sides (i : Fin 2) (b : Bool) : ν.real (side (S i) b)=2 := by
    cases b
    · rw [side_false]
      linarith [measureReal_add_measureReal_compl (μ:=ν) (hS i),hS2 i]
    · exact hS2 i
  let lwt := fun (b : Bool) => if b then p else q
  let rwt := fun (b : Bool) => if b then r else s
  have glue (b c : Bool) (C : ℝ) (C2 : C<2)
      (fill : FourCellFill (ν.real (sigCell (side (S 0) b) (side (S 1) c) (false,false)))
        (5-(lwt b+rwt c)) (lwt b) (rwt c) C) :
      ∃ H : Half μ,halfEnergy μ K H<1/50 := by
    obtain ⟨f,fm,fb,fmass,fcost⟩ := realize_four_cells ν (side (S 0) b) (side (S 1) c)
      (side_meas _ (hS 0) b) (side_meas _ (hS 1) c) full (sides 0 b) (sides 1 c)
      (5-(lwt b+rwt c)) (lwt b) (rwt c) C fill
    let o : Fin 2→Bool := ![b,c]
    let m : Fin 2→ℝ := ![lwt b/10,rwt c/10]
    have caps (j : Fin 2) : 0≤m j ∧ m j≤μ.real (B j (o j)) := by
      fin_cases j
      · have m0 := mB 0 b
        change μ.real (B 0 b)=lwt b/10 at m0
        change 0≤lwt b/10 ∧ lwt b/10≤μ.real (B 0 b)
        rw [←m0]
        exact ⟨measureReal_nonneg,le_rfl⟩
      · have m1 := mB 1 c
        change μ.real (B 1 c)=rwt c/10 at m1
        change 0≤rwt c/10 ∧ rwt c/10≤μ.real (B 1 c)
        rw [←m1]
        exact ⟨measureReal_nonneg,le_rfl⟩
    have mass : (∑ j,m j)=(5-(5-(lwt b+rwt c)))/10 := by
      rw [Fin.sum_univ_two]
      change lwt b/10+rwt c/10=_
      ring
    have cost : (∫ x, (∑ j : Fin 2,(side (S j) (o j)).indicator
        (fun _ => 10*m j) x)*f x ∂ν)≤C := by
      simp only [Fin.sum_univ_two,o,m,Matrix.cons_val_zero,Matrix.cons_val_one]
      convert fcost using 2 <;> ring_nf
    obtain ⟨H,hH⟩ := join_rectangles μ K A hA (fun j => B j (o j)) (fun j => side (S j) (o j))
      (fun j => hB j _) (fun i j e => hD i j _ _ e) (fun j => hOut j _) m caps
      (fun i j => outside i j _ _ (congrArg o)) (fun j => cross j _) anchor
      f fm fb _ C fmass mass cost
    exact ⟨H,hH.trans_lt (by linarith)⟩
  rcases favorable_flip ν (S 0) (S 1) (hS 0) (hS 1) full (hS2 0) (hS2 1) with al | cr
  · let x := ν.real (sigCell (S 0) (S 1) (false,false))
    have x2 : x≤2 := (four_cell_mass ν (S 0) (S 1) (hS 0) (hS 1) full (hS2 0) (hS2 1)).2.1
    obtain ⟨⟨C,C2,F⟩,_⟩ := two_heavy_profiles_of_scalar h p q r s L x hq hs hqp hsr hpr hr2 hscalar al x2
    exact glue true true C C2 F
  · let x := ν.real (sigCell (S 0) (S 1)ᶜ (false,false))
    have x2 : x≤2 := (four_cell_mass ν (S 0) (S 1)ᶜ (hS 0) (hS 1).compl full
      (hS2 0) (sides 1 false)).2.1
    obtain ⟨_,prof⟩ := two_heavy_profiles_of_scalar h p q r s L x hq hs hqp hsr hpr hr2 hscalar cr x2
    rcases prof with ⟨C,C2,F⟩|⟨C,C2,F⟩
    · exact glue true false C C2 (fill_unsort F)
    · obtain ⟨_,_,_,m1,m2⟩ := four_cell_mass ν (S 0) (S 1) (hS 0) (hS 1) full (hS2 0) (hS2 1)
      have E : ν.real (sigCell (S 0)ᶜ (S 1) (false,false))=x := by
        change ν.real (((S 0)ᶜ)ᶜ ∩ (S 1)ᶜ)=ν.real ((S 0)ᶜ∩((S 1)ᶜ)ᶜ)
        rw [compl_compl,compl_compl]
        exact m1.trans m2.symm
      apply glue false true C C2
      change FourCellFill (ν.real (sigCell (S 0)ᶜ (S 1) (false,false))) (5-(q+r)) q r C
      rw [E,add_comm q r]
      exact fill_flip (fill_unsort F)

theorem two_heavy_kernel (K : Kernel X) (A : Set X) (hA : MeasurableSet A)
    (B : Fin 2→Bool→Set X) (S : Fin 2→Set X)
    (hB : ∀ i b,MeasurableSet (B i b)) (hS : ∀ i,MeasurableSet (S i))
    (hD : ∀ i j b c,i≠j → Disjoint (B i b) (B j c))
    (hOut : ∀ i b,Disjoint A (B i b))
    (anchor : ∀ᵐ z ∂(μ.restrict A).prod (μ.restrict A),K.W z=0)
    (outside : ∀ i j b c,(i=j→b=c) →
      ∀ᵐ z ∂(μ.restrict (B i b)).prod (μ.restrict (B j c)),K.W z=0)
    (cross : ∀ i b,∀ᵐ z ∂(μ.restrict A).prod (μ.restrict (B i b)),
      K.W z=(side (S i) b).indicator (fun _ => (1:ℝ)) z.1)
    (hA4 : ((10:ℝ≥0∞) • μ.restrict A).real univ=4)
    (hS2 : ∀ i,((10:ℝ≥0∞) • μ.restrict A).real (S i)=2)
    (h p q r s L V θ : ℝ)
    (mB : ∀ i b, μ.real (B i b) =
      ((![if b then p else q,if b then r else s] : Fin 2→ℝ) i)/10)
    (hθ : 1≤θ) (hh : 0≤h) (hL : 0≤L)
    (hq : 1<q) (hs : 1<s) (hqp : q≤p) (hsr : s≤r) (hpr : p≤r) (hr2 : r≤2)
    (hV : V≤g L) (total : h+p+q+r+s+L=6)
    (hpiv : p+q≤2+h) (hriv : r+s≤2+h)
    (bad : 2≤q*min θ p+s*min θ r+V-θ) :
    ∃ H : Half μ,halfEnergy μ K H<1/50 := by
  have outcome := two_heavy_endpoint h p q r s L V θ hθ hh hL hq hs hqp hsr hpr hV total hpiv hriv bad
  exact two_heavy_kernel_of_scalar μ K A hA B S hB hS hD hOut anchor outside cross hA4 hS2
    h p q r s L mB hq hs hqp hsr hpr hr2 outcome.1 outcome.2

#print axioms two_heavy_kernel_of_scalar
#print axioms two_heavy_kernel
end SparseHalfCountableEndpoint
