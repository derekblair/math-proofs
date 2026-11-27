import GeometricGramBorder
import GeometricChart
import GeometricIIDAnchor

namespace RobustFolkman.GeometricGap
open MeasureTheory Matrix Set
open scoped ENNReal InnerProductSpace

def pairStepMap (k : ℕ) : PairCoord (Fin k) ⊕ Fin k → PairCoord (Fin (k+1)) :=
  Sum.elim
    (fun p => ⟨(p.val.1.castSucc,p.val.2.castSucc),Fin.castSucc_lt_castSucc_iff.mpr p.property⟩)
    (fun i => ⟨(i.castSucc,Fin.last k),Fin.castSucc_lt_last i⟩)

theorem pairStepMap_bijective (k : ℕ) : Function.Bijective (pairStepMap k) := by
  constructor
  · intro a b h
    have h1 := congrArg (fun j : PairCoord (Fin (k+1)) => j.val.1) h
    have h2 := congrArg (fun j : PairCoord (Fin (k+1)) => j.val.2) h
    rcases a with a|a <;> rcases b with b|b
    · exact congrArg Sum.inl (Subtype.ext (Prod.ext (Fin.castSucc_injective k h1) (Fin.castSucc_injective k h2)))
    · exact (Fin.ne_of_lt (Fin.castSucc_lt_last a.val.2) h2).elim
    · exact (Fin.ne_of_lt (Fin.castSucc_lt_last b.val.2) h2.symm).elim
    · exact congrArg Sum.inr (Fin.castSucc_injective k h1)
  · rintro ⟨⟨i,j⟩,h⟩
    have i0 : i ≠ Fin.last k := (Fin.lt_last_iff_ne_last).mp (h.trans_le (Fin.le_last j))
    let a := i.castPred i0
    have ai : a.castSucc=i := Fin.castSucc_castPred _ _
    by_cases top : j=Fin.last k
    · exact ⟨Sum.inr a, Subtype.ext (Prod.ext ai top.symm)⟩
    · let b := j.castPred top
      have bj : b.castSucc=j := Fin.castSucc_castPred _ _
      have ab : a<b := by
        apply Fin.castSucc_lt_castSucc_iff.mp
        rwa [ai,bj]
      exact ⟨Sum.inl ⟨(a,b),ab⟩,Subtype.ext (Prod.ext ai bj)⟩

noncomputable def pairStepIdx (k : ℕ) :
    PairCoord (Fin k) ⊕ Fin k ≃ PairCoord (Fin (k+1)) :=
  Equiv.ofBijective (pairStepMap k) (pairStepMap_bijective k)

noncomputable def chartStep (k : ℕ) :
    (PairCoord (Fin (k+1))→ℝ) ≃ᵐ ((PairCoord (Fin k)→ℝ) × (Fin k→ℝ)) :=
  (MeasurableEquiv.arrowCongr' (pairStepIdx k).symm (MeasurableEquiv.refl ℝ)).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : PairCoord (Fin k)⊕Fin k => ℝ))

theorem chartStep_volume (k : ℕ) :
    MeasurePreserving (chartStep k) volume volume :=
  (volume_measurePreserving_sumPiEquivProdPi _).comp
    (volume_preserving_arrowCongr' (pairStepIdx k).symm (MeasurableEquiv.refl ℝ)
      (MeasurePreserving.id _))

theorem chartStep_coords (k : ℕ) (x : PairCoord (Fin (k+1))→ℝ) :
    chartStep k x =
      (fun p => x (pairStepMap k (.inl p)),fun i => x (pairStepMap k (.inr i))) := rfl

#print axioms chartStep_volume
end RobustFolkman.GeometricGap
