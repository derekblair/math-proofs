import TriangleCutContinuity

open MeasureTheory Set Function
open scoped BigOperators

namespace SparseHalfGraphon
variable {X : Type*} [MeasurableSpace X]

/-- Cut distance controls edit/L¹ distance to a finite binary step
template without any quasi-randomness or pointwise convergence assumption. -/
theorem cut_to_binary_L1 (μ : Measure X) [IsFiniteMeasure μ]
    (K J : Kernel X) (ε:ℝ) (hcut : CutBound μ K J ε)
    {ι : Type*} [Fintype ι] (c : X→ι) (hc : ∀ i, MeasurableSet {x | c x=i})
    (b : ι→ι→Bool) (hj : ∀ x y, J.W (x,y)=(if b (c x) (c y) then 1 else 0)) :
    (∫ z, |gapW K J z| ∂μ.prod μ)≤(Fintype.card ι:ℝ)^2*ε := by
  classical
  let S : ι→Set X := fun i => {x | c x=i}
  let B : ι×ι→Set (X×X) := fun p => S p.1 ×ˢ S p.2
  have hm (p : ι×ι) : MeasurableSet (B p) := (hc _).prod (hc _)
  have hdis : Pairwise (Disjoint on B) := by
    intro p q hpq
    apply Set.disjoint_left.mpr
    intro z hz hz'
    change c z.1=p.1 ∧ c z.2=p.2 at hz
    change c z.1=q.1 ∧ c z.2=q.2 at hz'
    exact hpq (Prod.ext (hz.1.symm.trans hz'.1) (hz.2.symm.trans hz'.2))
  have hu : (⋃ p, B p)=univ := by
    ext z
    simp only [mem_iUnion,mem_univ,iff_true]
    exact ⟨(c z.1,c z.2),rfl,rfl⟩
  have hg : Integrable (gapW K J) (μ.prod μ) := by
    exact Integrable.of_bound (K.measurable_W.sub J.measurable_W).aestronglyMeasurable 1
      (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using gapW_bound K J z))
  have hterm (p : ι×ι) : (∫ z in B p, |gapW K J z| ∂μ.prod μ)≤ε := by
    have ht : |∫ z in B p, gapW K J z ∂μ.prod μ|≤ε := by
      have hs := setIntegral_prod (gapW K J) (s:=S p.1) (t:=S p.2) hg.integrableOn
      change |∫ z in S p.1 ×ˢ S p.2, gapW K J z ∂μ.prod μ|≤ε
      rw [hs]
      exact hcut (S p.1) (S p.2) (hc _) (hc _)
    cases hb : b p.1 p.2
    · have he (z : X×X) (hz : z∈B p) : |gapW K J z|=gapW K J z := by
        have hi : c z.1=p.1 ∧ c z.2=p.2 := hz
        have hh := hj z.1 z.2
        rw [hi.1,hi.2,hb] at hh
        simp at hh
        apply abs_of_nonneg
        have hz' : J.W z=0 := hh
        simpa [gapW,hz'] using K.nonneg z
      rw [setIntegral_congr_fun (hm p) he]
      exact (le_abs_self _).trans ht
    · have he (z : X×X) (hz : z∈B p) : |gapW K J z|= -gapW K J z := by
        have hi : c z.1=p.1 ∧ c z.2=p.2 := hz
        have hh := hj z.1 z.2
        rw [hi.1,hi.2,hb] at hh
        simp at hh
        apply abs_of_nonpos
        have hz' : J.W z=1 := hh
        simpa [gapW,hz',sub_nonpos] using K.le_one z
      rw [setIntegral_congr_fun (hm p) he,integral_neg]
      exact (neg_le_abs _).trans ht
  rw [← setIntegral_univ,← hu,
    integral_iUnion_fintype hm hdis (fun _ => hg.abs.integrableOn)]
  calc
    _ ≤ ∑ _ : ι×ι, ε := Finset.sum_le_sum (fun p _ => hterm p)
    _ = _ := by simp [Fintype.card_prod,pow_two,mul_assoc]

#print axioms cut_to_binary_L1
end SparseHalfGraphon
