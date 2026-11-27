import PetersenCells
import ThreeUnitKernel

open Set MeasureTheory SparseHalfGraphon
open scoped ENNReal
namespace SparseHalfCountableEndpoint
open PetersenParity
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

private theorem real_scale_restrict (A T : Set X) (hT : MeasurableSet T) :
    ((10:ℝ≥0∞) • μ.restrict A).real T=10*μ.real (A∩T) := by
  unfold Measure.real
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,Measure.restrict_apply hT,inter_comm]
  norm_num

private theorem parity_even_masses (A : Set X) (S : Fin 3→Set X)
    (hS : ∀ i,MeasurableSet (S i))
    (par : ∀ a b c : Bool, ((10:ℝ≥0∞) • μ.restrict A).real
        (tripleCell (S 0) (S 1) (S 2) (a,b,c))=
        if xor (xor a b) c=false then (1:ℝ) else 0) :
    ∀ i : Fin 4, μ.real (A∩tripleCell (S 0) (S 1) (S 2) (pattern i))=1/10 := by
  intro i
  have x := par (bit i 0) (bit i 1) (bit i 2)
  rw [pattern_even i, ite_eq_left rfl,real_scale_restrict μ A _ (tripleCell_meas _ _ _ (hS 0) (hS 1) (hS 2) _)] at x
  change 10*μ.real (A∩tripleCell (S 0) (S 1) (S 2) (pattern i))=1 at x
  linarith

/-- Full measurable rigidity for the three unit complementary pairs,
including either surviving parity, deleted edges, and output with
an exact balanced measurable label. -/
theorem three_unit_completed_kernel (K : Kernel X) (A : Set X) (hA : MeasurableSet A)
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
    (hA4 : ((10:ℝ≥0∞) • μ.restrict A).real univ=4)
    (hS2 : ∀ i, ((10:ℝ≥0∞) • μ.restrict A).real (S i)=2)
    (prob : μ.real univ=1) :
    (∃ H : Half μ, halfEnergy μ K H<1/50) ∨
      (∃ g : X→Fin 10, Measurable g ∧ (∀ i,μ.real (cell g i)=1/10) ∧
        K.W =ᵐ[μ.prod μ] (fun z => edgeReal (adjacent (g z.1) (g z.2)))) := by
  have dif (i j : Fin 3) (b c : Bool) (ne : i≠j) : Disjoint (P i b) (P j c) :=
    @hD (i,b) (j,c) (fun h => ne (congrArg (fun w : Fin 3×Bool => w.1) h))
  rcases three_unit_kernel μ K A hA P S hP hS dif hOut hM anchor outside cross hA4 hS2 with
    strict | ⟨v,par⟩
  · exact Or.inl strict
  cases v
  · exact petersen_even_kernel μ K A hA P S hP hS hD hOut hM anchor outside cross prob
      (parity_even_masses μ A S hS par)
  · let fl := fun i : Fin 3 => fun b : Bool => if i=0 then !b else b
    let T := fun i : Fin 3 => if i=0 then (S i)ᶜ else S i
    let Q := fun i b => P i (fl i b)
    have flinj (i : Fin 3) : Function.Injective (fl i) := by
      intro a b h
      by_cases e : i=0
      · simpa [fl,e] using congrArg Bool.not h
      · simpa [fl,e] using h
    have qm (i : Fin 3) (b : Bool) : MeasurableSet (Q i b) := hP i _
    have tm (i : Fin 3) : MeasurableSet (T i) := by
      by_cases e : i=0
      · rw [show T i=(S i)ᶜ by simp [T,e]]
        exact (hS i).compl
      · rw [show T i=S i by simp [T,e]]
        exact hS i
    have qd : Pairwise fun i j : Fin 3×Bool => Disjoint (Q i.1 i.2) (Q j.1 j.2) := by
      intro i j ne
      refine @hD (i.1,fl i.1 i.2) (j.1,fl j.1 j.2) ?_
      intro h
      have e0 := congrArg (fun w : Fin 3×Bool => w.1) h
      have e : i.1=j.1 := e0
      have g : fl j.1 i.2=fl j.1 j.2 := by
        rw [←e]
        exact (congrArg (fun w : Fin 3×Bool => w.2) h).trans (congrArg (fun k => fl k j.2) e.symm)
      exact ne (Prod.ext e (flinj _ g))
    have qo (i j : Fin 3) (b c : Bool) (h : i=j→b=c) :
        ∀ᵐ z ∂(μ.restrict (Q i b)).prod (μ.restrict (Q j c)),K.W z=0 := by
      apply outside
      intro e
      subst j
      rw [h rfl]
    have cq (i : Fin 3) (b : Bool) : ∀ᵐ z ∂(μ.restrict A).prod (μ.restrict (Q i b)),
        K.W z=(side (T i) b).indicator (fun _ => (1:ℝ)) z.1 := by
      have x : side (T i) b=side (S i) (fl i b) := by
        by_cases e : i=0
        · cases b <;> simp [T,fl,e]
        · simp [T,fl,e]
      rw [x]
      exact cross i (fl i b)
    have pm (i : Fin 4) :
        μ.real (A∩tripleCell (T 0) (T 1) (T 2) (pattern i))=1/10 := by
      have t0 : T 0=(S 0)ᶜ := by simp [T]
      have t1 : T 1=S 1 := by simp [T]
      have t2 : T 2=S 2 := by simp [T]
      rw [t0,t1,t2]
      change μ.real (A ∩ tripleCell (S 0)ᶜ (S 1) (S 2) (bit i 0,bit i 1,bit i 2))=_
      rw [flip_first]
      have eq : ∀ i : Fin 4, xor (xor (!bit i 0) (bit i 1)) (bit i 2)=true := by decide
      have h := par (!bit i 0) (bit i 1) (bit i 2)
      rw [eq i,ite_eq_left rfl,real_scale_restrict μ A _ (tripleCell_meas _ _ _ (hS 0) (hS 1) (hS 2) _)] at h
      linarith
    exact petersen_even_kernel μ K A hA Q T qm tm qd (fun i b => hOut i _) (fun i b => hM i _)
      anchor qo cq prob pm

#print axioms three_unit_completed_kernel
end SparseHalfCountableEndpoint
