import RibbonOddLabels
import RibbonOrder3Nonstationary

namespace RibbonOddFinite
open RibbonOrderThree RibbonOdd RibbonOrder3
universe u

theorem mixed_from_field (cover : FieldCover.{u,u} Bad) : MixedOrder3Cover.{u} := by
  intro G K _ _ _ _ m x y μ τ odd two order co norm _ _
  rcases cover m x y μ τ two odd co norm with already|⟨p,hp,f,a,b,ax,byy,h⟩
  · exact already
  obtain ⟨i,ei⟩ := h
  have pi : p=(inputs i).p := (Prod.mk.inj ei).1
  subst p
  letI : Fact (inputs i).p.Prime := ⟨inputs_prime i⟩
  have ev := Prod.mk.inj ((Prod.mk.inj ei).2)
  have A : digit (inputs i).p (inputs i).a=a := by
    rw [←ZMod.natCast_zmod_val a]
    exact congrArg (digit _) ev.1.symm
  have B : digit (inputs i).p (inputs i).b=b := by
    rw [←ZMod.natCast_zmod_val b]
    exact congrArg (digit _) ev.2.symm
  have tx : f (coeffX (inputs i).p (inputs i).a)=τ x := by
    rcases norm with ⟨nz,x0,_⟩|⟨zz,_,x1,_⟩
    · have N : (inputs i).a≠1 := by
        intro h
        exact nz (by change (μ x:K)=1; rw [←ax,←A,(digit_one i).2 h,map_one])
      simp [coeffX,N,x0]
    · have Z : (inputs i).a=1 := (digit_one i).1 (f.injective (by rw [A,ax,map_one]; exact zz))
      simp [coeffX,Z,x1]
  have ty : f (coeffY (inputs i).p (inputs i).a)=τ y := by
    rcases norm with ⟨nz,_,y1⟩|⟨zz,_,_,y0⟩
    · have N : (inputs i).a≠1 := by
        intro h
        exact nz (by change (μ x:K)=1; rw [←ax,←A,(digit_one i).2 h,map_one])
      simp [coeffY,N,y1]
    · have Z : (inputs i).a=1 := (digit_one i).1 (f.injective (by rw [A,ax,map_one]; exact zz))
      simp [coeffY,Z,y0]
  exact Or.inr (Or.inr (Or.inr (joint (RibbonP11Adapters.dnil m) x y order i μ τ co f
    (by rw [A,ax]) (by rw [B,byy]) tx ty)))

end RibbonOddFinite
#print axioms RibbonOddFinite.mixed_from_field
