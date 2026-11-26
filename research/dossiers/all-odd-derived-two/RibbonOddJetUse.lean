import RibbonOddLabels
import RibbonOddJetSorted
import RibbonOddJetScale

namespace RibbonOddFinite
open RibbonOrderThree RibbonStationaryWord RibbonP11Charts RibbonStationaryChart
open RibbonDerived3 Ribbon5Bridge
universe u
variable {G : Type u} [Group G]

theorem jet_sound (i : Fin 28) (x y : G)
    (μ : G→*(J i)ˣ) (τ : G→J i) (co : Aff μ τ)
    (lab : RibbonOdd.JetLabel (inputs i).p μ x y=inputLabel i)
    (norm : RibbonP11.Normalized (TrivSqZeroExt.fstHom (F i) (F i) (F i)).toRingHom x y μ τ)
    (k : Count) (p q : Fin 64)
    (e : pathAt x y (spec k).T.toArray p.val=pathAt x y (spec k).T.toArray q.val) :
    jetPoint i (μ x:J i).snd (μ y:J i).snd k p=jetPoint i (μ x:J i).snd (μ y:J i).snd k q := by
  let z := inputs i
  letI : Fact z.p.Prime := ⟨inputs_prime i⟩
  let da : F i := (μ x:J i).snd
  let db : F i := (μ y:J i).snd
  have V := Prod.mk.inj ((Prod.mk.inj lab).2)
  have xx : (μ x:J i).fst=digit z.p z.a := by
    rw [←ZMod.natCast_zmod_val (μ x:J i).fst]
    exact congrArg (digit z.p) V.1
  have yy : (μ y:J i).fst=digit z.p z.b := by
    rw [←ZMod.natCast_zmod_val (μ y:J i).fst]
    exact congrArg (digit z.p) V.2
  have X : (μ x:J i)=jet (digit z.p z.a) da := TrivSqZeroExt.ext xx rfl
  have Y : (μ y:J i)=jet (digit z.p z.b) db := TrivSqZeroExt.ext yy rfl
  have h := invert_inputs i
  have a := RibbonP11Pair.inv_unit_of (μ x) (jetInv (digit z.p z.a) da)
    (by rw [X]; exact jet_mul_inv _ _ h.1)
  have b := RibbonP11Pair.inv_unit_of (μ y) (jetInv (digit z.p z.b) db)
    (by rw [Y]; exact jet_mul_inv _ _ h.2)
  have tx : τ x=jet (coeffX z.p z.a) 0 := by
    rcases norm with ⟨nz,x0,_⟩|⟨zz,_,x1,_⟩
    · have N : z.a≠1 := fun h => nz (xx.trans ((digit_one i).2 h))
      simp [x0,coeffX,N,jet] <;> rfl
    · have Z : z.a=1 := (digit_one i).1 (xx.symm.trans zz)
      simp [x1,coeffX,Z,jet] <;> rfl
  have ty : τ y=jet (coeffY z.p z.a) 0 := by
    rcases norm with ⟨nz,_,y1⟩|⟨zz,_,_,y0⟩
    · have N : z.a≠1 := fun h => nz (xx.trans ((digit_one i).2 h))
      simp [y1,coeffY,N,jet] <;> rfl
    · have Z : z.a=1 := (digit_one i).1 (xx.symm.trans zz)
      simp [y0,coeffY,Z,jet] <;> rfl
  change jetPoint i da db k p=jetPoint i da db k q
  simpa only [X,Y,a,b,tx,ty,jetPoint,coefficients] using
    flatPosition_same μ τ co x y (spec k) p.val q.val e

theorem jets_cover : RibbonOdd.JetCover.{u} Bad := by
  intro G _ _ m x y p _ μ τ _ co norm lab fresh
  obtain ⟨i,ei⟩ := lab
  have ep : p=(inputs i).p := (Prod.mk.inj ei).1
  subst p
  let da := (μ x:J i).snd
  let db := (μ y:J i).snd
  obtain ⟨s,d,hs⟩ := canonical_direction da db fresh
  have a : s*da=(direction i d).1 := congrArg Prod.fst hs
  have b : s*db=(direction i d).2 := congrArg Prod.snd hs
  let k := pickJet i d
  let chart (p : Fin 64) := jetPoint i (direction i d).1 (direction i d).2 k p
  apply Or.inr ∘ Or.inr ∘ Or.inr
  apply from_state (RibbonP11Adapters.dnil m) k x y chart
  · intro p q he
    have H := congrArg (fMap (scale s)) (jet_sound i x y μ τ co ei norm k p q he)
    change fMap (scale s) (jetPoint i da db k p) = fMap (scale s) (jetPoint i da db k q) at H
    rw [scale_point,scale_point,a,b] at H
    exact H
  · intro p q lt e
    exact jet_sorted_sound i d p q lt e

end RibbonOddFinite
#print axioms RibbonOddFinite.jets_cover
