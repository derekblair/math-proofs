import RibbonOddJetCore

namespace RibbonOddFinite
open RibbonOrderThree RibbonP11Charts RibbonStationaryWord Ribbon5Bridge
variable {i : Fin 28}

def scale (c : F i) : J i →+* J i where
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

theorem scale_jet (c a da : F i) : scale c (jet a da)=jet a (c*da) := rfl

theorem scale_jetInv (c a da : F i) : scale c (jetInv a da)=jetInv a (c*da) := by
  apply TrivSqZeroExt.ext
  · rfl
  · change c * -(da*(a^((inputs i).p-2))^2) = -(c*da*(a^((inputs i).p-2))^2)
    ring

def fMap (f : J i→+*J i) (s : Flat (J i)) : Flat (J i) := (s.1,f s.2.1,f s.2.2)

theorem step_map (f : J i→+*J i) (a ai b bi tx ty : J i) (s : Flat (J i)) (p : P) :
    fMap f (flatStep a ai b bi tx ty s p) =
      flatStep (f a) (f ai) (f b) (f bi) (f tx) (f ty) (fMap f s) p := by
  rcases s with ⟨s,m,t⟩
  cases s <;> fin_cases p <;> simp [fMap,flatStep]

theorem fold_map (f : J i→+*J i) (a ai b bi tx ty : J i) (l : List P) (s : Flat (J i)) :
    fMap f (l.foldl (flatStep a ai b bi tx ty) s) =
      l.foldl (flatStep (f a) (f ai) (f b) (f bi) (f tx) (f ty)) (fMap f s) := by
  induction l generalizing s with
  | nil => rfl
  | cons p l ih => simp only [List.foldl_cons,ih,step_map]

theorem scale_point (c : F i) (da db : F i) (k : Count) (p : Fin 64) :
    fMap (scale c) (jetPoint i da db k p)=jetPoint i (c*da) (c*db) k p := by
  simp only [jetPoint,coefficients,flatPosition]
  rw [fold_map]
  simp only [scale_jet,scale_jetInv,mul_zero,fMap,map_one,map_zero]

theorem jet_mul_inv (a da : F i) (h : a*a^((inputs i).p-2)=1) :
    jet a da*jetInv a da=1 := by
  apply TrivSqZeroExt.ext
  · exact h
  · let ap := a^((inputs i).p-2)
    change a * -(da*ap^2) + da*ap=0
    calc
      _ = da*ap - (a*ap)*(da*ap) := by ring
      _ = 0 := by rw [show a*ap=1 from h,one_mul,sub_self]

theorem canonical_direction (da db : F i) (h : da≠0 ∨ db≠0) :
    ∃ (c : F i) (d : Dir i), (c*da,c*db)=direction i d := by
  letI : Fact (inputs i).p.Prime := ⟨inputs_prime i⟩
  by_cases a : da=0
  · have b := h.resolve_left (fun z => z a)
    exact ⟨db⁻¹,0,by simp [a,b,direction]⟩
  · let s := da⁻¹*db
    have sv := ZMod.val_lt s
    refine ⟨da⁻¹,⟨s.val+1,by omega⟩,?_⟩
    have d0 : s.val+1≠0 := by omega
    simp only [direction,d0,if_false,Nat.add_sub_cancel,ZMod.natCast_zmod_val]
    exact Prod.ext (inv_mul_cancel₀ a) rfl

end RibbonOddFinite
#print axioms RibbonOddFinite.canonical_direction
