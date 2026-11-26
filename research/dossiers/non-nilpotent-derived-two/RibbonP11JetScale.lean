import RibbonP11JetCalc
namespace RibbonP11JetCalc
open RibbonP11Pair RibbonP11Charts RibbonStationaryWord Ribbon5Bridge
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

def scale (c : F) : J →+* J where
  toFun v := jet v.fst (c*v.snd)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp [jet]
  map_one' := by apply TrivSqZeroExt.ext <;> simp [jet]
  map_add' u v := by
    apply TrivSqZeroExt.ext
    · rfl
    · change c*(u.snd+v.snd)=c*u.snd+c*v.snd
      ring
  map_mul' u v := by
    apply TrivSqZeroExt.ext
    · rfl
    · change c*(u.fst*v.snd+u.snd*v.fst)=u.fst*(c*v.snd)+(c*u.snd)*v.fst
      ring

theorem scale_jet (c a da : F) : scale c (jet a da)=jet a (c*da) := rfl

theorem scale_jetInv (c a da : F) : scale c (jetInv a da)=jetInv a (c*da) := by
  apply TrivSqZeroExt.ext
  · rfl
  · change c * -(da*(a^9)^2) = -(c*da*(a^9)^2)
    ring

def fMap (f : J→+*J) (s : Flat J) : Flat J := (s.1,f s.2.1,f s.2.2)

theorem step_map (f : J→+*J) (a ai b bi tx ty : J) (s : Flat J) (p : P) :
    fMap f (flatStep a ai b bi tx ty s p) =
      flatStep (f a) (f ai) (f b) (f bi) (f tx) (f ty) (fMap f s) p := by
  rcases s with ⟨s,m,t⟩
  cases s <;> fin_cases p <;> simp [fMap,flatStep]

theorem fold_map (f : J→+*J) (a ai b bi tx ty : J) (l : List P) (s : Flat J) :
    fMap f (l.foldl (flatStep a ai b bi tx ty) s) =
      l.foldl (flatStep (f a) (f ai) (f b) (f bi) (f tx) (f ty)) (fMap f s) := by
  induction l generalizing s with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldl_cons,ih,step_map]

theorem scale_point (c : F) (i : Fin 16) (da db : F) (k : Count) (p : Fin 64) :
    fMap (scale c) (jetPoint i da db k p)=jetPoint i (c*da) (c*db) k p := by
  simp only [jetPoint,coefficients,flatPosition]
  rw [fold_map]
  simp only [scale_jet,scale_jetInv,mul_zero,fMap,map_one,map_zero]

end RibbonP11JetCalc
#print axioms RibbonP11JetCalc.scale_point
