import StrictDominantActive
import SaturatedActivePairs

open Set MeasureTheory Function Filter
namespace SparseHalfGraphon
variable {X I : Type*} [MeasurableSpace X] [Countable I]
variable (μ : Measure X) [IsFiniteMeasure μ]

/-- Adapter accepting the saturated pair output with its dummy empty cells
and with outside restrictions on the row measure. -/
theorem strict_dominant_saturated (K : Kernel X) (A S : Set X)
    (ma : MeasurableSet A) (ms : MeasurableSet S) (ad : Disjoint A S)
    (asize : μ.real A=2/5) (size : μ.real S=3/5)
    (aa : ∀ᵐ z ∂μ.prod μ, z.1∈A → z.2∈A → K.W z=0)
    (P Q C : I→Set X) (mp : ∀ i, MeasurableSet (P i))
    (mq : ∀ i, MeasurableSet (Q i)) (mc : ∀ i, MeasurableSet (C i))
    (ins : ∀ i, P i∪Q i⊆S) (inner : ∀ i, Disjoint (P i) (Q i))
    (outer : Pairwise (Disjoint on fun i=>P i∪Q i))
    (edge : ∀ᵐ z ∂(μ.restrict S).prod (μ.restrict S), 0<K.W z →
      ∃ i, (z.1∈P i ∧ z.2∈Q i) ∨ (z.1∈Q i ∧ z.2∈P i))
    (prof : ∀ i, (P i=∅ ∧ Q i=∅) ∨
      ((μ.restrict A).real (C i)=mass (μ.restrict A)/2 ∧
       (μ.restrict A).real (C i)ᶜ=mass (μ.restrict A)/2 ∧
       (∀ᵐ x ∂(μ.restrict S).restrict (P i),
          (fun y=>K.W (x,y)) =ᵐ[μ.restrict A] oneOn (C i)) ∧
       (∀ᵐ x ∂(μ.restrict S).restrict (Q i),
          (fun y=>K.W (x,y)) =ᵐ[μ.restrict A] oneOn (C i)ᶜ)))
    (j : I) (hp : 1<10*μ.real (P j)) (hq : 1<10*μ.real (Q j))
    (hp2 : 10*μ.real (P j)≤2) (hq2 : 10*μ.real (Q j)≤2)
    (ex : 2+10*μ.real (S\⋃ i,P i∪Q i)<10*μ.real (P j)+10*μ.real (Q j)) :
    ∃ H : Half μ, halfEnergy μ K H<1/50 := by
  classical
  let D (i : I) := if P i=∅ ∧ Q i=∅ then C j else C i
  have md (i) : MeasurableSet (D i) := by by_cases h:P i=∅ ∧ Q i=∅ <;> simp [D,h,mc]
  have cap (i : I) (a b : ℝ)
      (p : (μ.restrict A).real (C i)=a) (q : (μ.restrict A).real (C i)ᶜ=b) :
      μ.real (C i∩A)=a ∧ μ.real ((C i)ᶜ∩A)=b := by
    simpa only [measureReal_def,Measure.restrict_apply (mc i),Measure.restrict_apply (mc i).compl]
      using And.intro p q
  have mn : mass (μ.restrict A)/2=1/5 := by
    rw [mass,measureReal_def,Measure.restrict_apply_univ,←measureReal_def,asize]
    norm_num
  have pivotCap : μ.real (C j∩A)=1/5 ∧ μ.real ((C j)ᶜ∩A)=1/5 := by
    rcases prof j with h|⟨h₁,h₂,_,_⟩
    · norm_num [h.1] at hp
    · exact cap j _ _ (h₁.trans mn) (h₂.trans mn)
  have restrict_eq (R : Set X) (m : MeasurableSet R) (s : R⊆S) :
      (μ.restrict S).restrict R = μ.restrict R := by
    rw [Measure.restrict_restrict m,inter_eq_left.mpr s]
  apply strict_dominant_active μ K A S ma ms ad size aa P Q D mp mq md ins inner outer edge
    _ _ _ j hp hq hp2 hq2 ex
  · intro i
    by_cases h:P i=∅ ∧ Q i=∅
    · simpa [D,h] using pivotCap
    · rcases prof i with u|⟨h₁,h₂,_,_⟩
      · contradiction
      · simpa [D,h] using cap i _ _ (h₁.trans mn) (h₂.trans mn)
  · intro i
    by_cases h:P i=∅ ∧ Q i=∅
    · simp [h.1]
    · rcases prof i with u|⟨_,_,row,_⟩
      · contradiction
      · rw [restrict_eq _ (mp i) (subset_union_left.trans (ins i))] at row
        simpa [D,h] using row
  · intro i
    by_cases h:P i=∅ ∧ Q i=∅
    · simp [h.2]
    · rcases prof i with u|⟨_,_,_,row⟩
      · contradiction
      · rw [restrict_eq _ (mq i) (subset_union_right.trans (ins i))] at row
        simpa [D,h] using row

#print axioms strict_dominant_saturated
end SparseHalfGraphon
