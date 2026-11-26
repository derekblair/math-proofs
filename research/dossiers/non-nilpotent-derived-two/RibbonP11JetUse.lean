import RibbonP11JetCert
import RibbonP11JetScale
import RibbonP11PairUse
namespace RibbonP11JetCalc
open RibbonP11Pair RibbonP11Charts RibbonStationaryWord RibbonStationaryChart RibbonDerived3 Ribbon5Bridge
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

theorem jet_mul_inv (a da : F) (h : a*a^9=1) : jet a da*jetInv a da=1 := by
  apply TrivSqZeroExt.ext
  · exact h
  · change a * -(da*(a^9)^2) + da*a^9=0
    calc
      _ = da*a^9 - (a*a^9)*(da*a^9) := by ring
      _ = 0 := by rw [h,one_mul,sub_self]

theorem direction_one : ∀ d : Fin 11,
    direction ⟨d.val+1,by omega⟩=(1,(d.val:F)) := by decide +kernel

theorem canonical_direction (da db : F) (h : da≠0 ∨ db≠0) :
    ∃ (c : F) (d : Fin 12), (c*da,c*db)=direction d := by
  by_cases a : da=0
  · have b := h.resolve_left (fun z => z a)
    exact ⟨db⁻¹,0,by simp [a,b,direction]⟩
  · let s := da⁻¹*db
    let u : Fin 11 := ⟨s.val,ZMod.val_lt s⟩
    refine ⟨da⁻¹,⟨u.val+1,by omega⟩,?_⟩
    rw [direction_one]
    exact Prod.ext (inv_mul_cancel₀ a) (ZMod.natCast_zmod_val s).symm

variable {G : Type*} [Group G]

structure Coeffs (x y : G) (i : Fin 16) (da db : F) where
  mu : G →* Jˣ
  tau : G → J
  aff : Aff mu tau
  mX : (mu x:J)=jet (bad i).1 da
  mY : (mu y:J)=jet (bad i).2 db
  tX : tau x=jet (if (bad i).1=1 then 1 else 0) 0
  tY : tau y=jet (if (bad i).1=1 then 0 else 1) 0

theorem Coeffs.sound {x y : G} {i : Fin 16} {da db : F}
    (c : Coeffs x y i da db) (k : Count) (p q : Fin 64)
    (e : pathAt x y (spec k).T.toArray p.val=pathAt x y (spec k).T.toArray q.val) :
    jetPoint i da db k p=jetPoint i da db k q := by
  have ix := inv_unit_of (c.mu x) (jetInv (bad i).1 da)
    (by rw [c.mX]; exact jet_mul_inv _ _ (bad_mul_pow i).1)
  have iy := inv_unit_of (c.mu y) (jetInv (bad i).2 db)
    (by rw [c.mY]; exact jet_mul_inv _ _ (bad_mul_pow i).2)
  have s := flatPosition_same c.mu c.tau c.aff x y (spec k) p.val q.val e
  simpa only [jetPoint,coefficients,ix,iy,c.mX,c.mY,c.tX,c.tY] using s

theorem one_jet (dnil : DLS G 2=⊥) (x y : G) (i : Fin 16) (da db : F)
    (h : da≠0 ∨ db≠0) (c : Coeffs x y i da db) :
    Ribbon.Cycle x y 32 ∨ Ribbon.Cycle x y 64 := by
  obtain ⟨s,d,eq⟩ := canonical_direction da db h
  let k := jetPick i d
  apply from_state dnil k x y (jetPoint i (direction d).1 (direction d).2 k)
  · intro p q he
    have P := congrArg (fMap (scale s)) (c.sound k p q he)
    have aa : s*da=(direction d).1 := congrArg Prod.fst eq
    have bb : s*db=(direction d).2 := congrArg Prod.snd eq
    rw [scale_point,scale_point,aa,bb] at P
    exact P
  · exact fun p q lt e => certified i d p q lt e

end RibbonP11JetCalc
#print axioms RibbonP11JetCalc.one_jet
