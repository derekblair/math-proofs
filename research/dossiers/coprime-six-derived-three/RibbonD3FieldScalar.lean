import RibbonD3FieldSlopeDrop
import RibbonAffineModCore

namespace RibbonD3Field
open RibbonAffine (pl mon eRow)
open RibbonStationaryField (Poly)
variable {K : Type*} [Field K]

abbrev Triple := Nat × Nat × Nat

def provisional : List Triple := [(11,3,1),(11,3,3),(11,3,4),(11,3,5),(11,3,9),(11,4,1),(11,4,3),(11,4,4),(11,4,5),(11,4,9),(11,5,1),(11,5,3),(11,5,4),(11,5,5),(11,5,9),(11,9,1),(11,9,3),(11,9,4),(11,9,5),(11,9,9),(23,3,1),(23,3,18),(23,4,1),(23,4,6),(23,4,13),(23,4,16),(23,6,1),(23,6,4),(23,6,9),(23,6,18),(23,8,1),(23,8,16),(23,9,1),(23,9,6),(23,9,9),(23,9,18),(23,13,1),(23,13,4),(23,13,13),(23,13,16),(23,16,1),(23,16,4),(23,16,8),(23,16,13),(23,18,1),(23,18,3),(23,18,6),(23,18,9),(23,18,18),(29,7,1),(29,7,20),(29,7,25),(29,16,1),(29,20,1),(29,20,7),(29,20,20),(29,20,24),(29,24,20),(29,25,1),(29,25,7),(29,25,25),(41,10,1),(43,21,1),(47,4,18),(47,7,8),(47,8,7),(47,12,18),(47,18,4),(47,18,12),(47,21,42),(47,25,37),(47,34,42),(47,37,25),(47,42,21),(47,42,34),(53,13,1),(53,36,42),(53,42,36),(53,49,49),(59,21,36),(59,25,26),(59,26,25),(59,27,41),(59,36,21),(59,41,27),(61,20,1),(67,22,1),(71,12,60),(71,43,50),(71,50,43),(71,60,12),(83,7,51),(83,7,70),(83,12,49),(83,17,78),(83,41,1),(83,49,12),(83,51,7),(83,70,7),(83,78,17),(101,25,1),(101,52,79),(101,79,52),(107,10,76),(107,16,79),(107,42,49),(107,49,42),(107,76,10),(107,79,16),(137,34,1),(139,45,112),(139,112,45),(173,43,1),(191,117,121),(191,121,117),(191,134,135),(191,135,134),(239,11,187),(239,187,11),(251,164,175),(251,175,164),(367,200,225),(367,225,200),(419,69,300),(419,300,69),(443,86,272),(443,90,109),(443,109,90),(443,272,86),(1319,691,974),(1319,974,691),(1487,227,1034),(1487,1034,227),(2903,454,1225),(2903,1225,454),(4231,1218,2083),(4231,2083,1218)]

/-- Scalar conclusions are exact in the ambient field, not heuristic
prime-field approximations. -/
def ScalarPair (a b : Kˣ) : Prop :=
  ∃ p x y : Nat, p.Prime ∧ (p:K)=0 ∧ (a:K)=(x:K) ∧ (b:K)=(y:K) ∧ (p,x,y)∈provisional

def scalarPower (p s ax bx : Nat) (u v : Int) : Prop :=
  if hp : p.Prime then
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    if hs : (s:ZMod p)≠0 then
      let z : (ZMod p)ˣ := Units.mk0 _ hs
      ((z^v : (ZMod p)ˣ):ZMod p)=(ax:ZMod p) ∧
        ((z^(-u) : (ZMod p)ˣ):ZMod p)=(bx:ZMod p)
    else False
  else False

instance (p s ax bx : Nat) (u v : Int) : Decidable (scalarPower p s ax bx u v) := by
  unfold scalarPower
  split
  · rename_i hp
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    dsimp only
    split <;> infer_instance
  · infer_instance

theorem scalar_power_sound (p s ax bx : Nat) (u v : Int) (H : scalarPower p s ax bx u v)
    (L : (p,ax,bx)∈provisional) (t : Kˣ) (P : (p:K)=0) (root : (t:K)=(s:K)) : ScalarPair (t^v) (t^(-u)) := by
  unfold scalarPower at H
  split at H
  · rename_i hp
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    dsimp only at H
    split at H
    · rename_i hs
      letI : CharP K p := (CharP.charP_iff_prime_eq_zero (R:=K) hp).mpr P
      let f : ZMod p→+*K := ZMod.castHom (dvd_refl p) K
      let U : (ZMod p)ˣ := Units.mk0 (s:ZMod p) hs
      have U' : Units.map f.toMonoidHom U=t := by
        apply Units.ext
        change f (s:ZMod p)=(t:K)
        rw [map_natCast,root]
      have A := congrArg f H.1
      have B := congrArg f H.2
      change f (((U^v : (ZMod p)ˣ):ZMod p))=f (ax:ZMod p) at A
      change f (((U^(-u) : (ZMod p)ˣ):ZMod p))=f (bx:ZMod p) at B
      change (↑(Units.map f.toMonoidHom (U^v)):K)=f (ax:ZMod p) at A
      change (↑(Units.map f.toMonoidHom (U^(-u))):K)=f (bx:ZMod p) at B
      rw [map_zpow,U',map_natCast] at A B
      exact ⟨p,ax,bx,hp,P,A,B,L⟩
    · exact False.elim H
  · exact False.elim H

theorem scalar_digit (p : Nat) (hp : p.Prime) (a b : Kˣ) (x y : Nat)
    (P : (p:K)=0) (AX : (a:K)=(x:K)) (BY : (b:K)=(y:K))
    (hx : x<p) (hy : y<p) :
    ∃ (e : ZMod p→+*K) (u v : ZMod p),
      e u=(a:K) ∧ e v=(b:K) ∧ u.val=x ∧ v.val=y := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : CharP K p := (CharP.charP_iff_prime_eq_zero (R:=K) hp).mpr P
  let f : ZMod p→+*K := ZMod.castHom (dvd_refl p) K
  refine ⟨f,(x:ZMod p),(y:ZMod p),by rw [map_natCast,AX],by rw [map_natCast,BY],?_,?_⟩
  · rw [ZMod.val_natCast,Nat.mod_eq_of_lt hx]
  · rw [ZMod.val_natCast,Nat.mod_eq_of_lt hy]

end RibbonD3Field
#print axioms RibbonD3Field.scalar_power_sound
