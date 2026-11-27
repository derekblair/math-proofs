import RibbonD3FieldScalar
import RibbonD3WideSlopeDrop
import RibbonAffineModCore

namespace RibbonD3Wide
open RibbonD3Field
open RibbonAffine (pl mon eRow)
open RibbonStationaryField (Poly)
variable {K : Type*} [Field K]

abbrev Triple := Nat × Nat × Nat

def provisional : List Triple := [(7,2,1),(7,2,2),(7,2,4),(7,4,1),(7,4,2),(7,4,4),(11,3,1),(11,3,3),(11,3,4),(11,3,5),(11,3,9),(11,4,1),(11,4,3),(11,4,4),(11,4,5),(11,4,9),(11,5,1),(11,5,3),(11,5,4),(11,5,5),(11,5,9),(11,9,1),(11,9,3),(11,9,4),(11,9,5),(11,9,9),(13,3,1),(13,3,3),(13,3,9),(13,9,1),(13,9,3),(13,9,9),(19,4,1),(19,4,4),(19,4,5),(19,5,1),(19,5,5),(19,7,1),(19,7,7),(19,7,11),(19,9,9),(19,11,1),(19,11,7),(19,11,11),(19,17,1),(19,17,9),(23,3,1),(23,4,1),(23,6,1),(23,8,1),(23,9,1),(23,9,9),(23,9,18),(23,13,1),(23,16,1),(23,18,1),(23,18,9),(23,18,18),(29,7,1),(29,16,1),(29,20,1),(29,25,1),(43,23,16),(43,25,1),(43,31,1)]

/-- Scalar conclusions are exact in the ambient field, not heuristic
prime-field approximations. -/
def ScalarPair (a b : Kˣ) : Prop :=
  ∃ p x y : Nat, p.Prime ∧ (p:K)=0 ∧ (a:K)=(x:K) ∧ (b:K)=(y:K) ∧ (p,x,y)∈provisional

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


end RibbonD3Wide
#print axioms RibbonD3Wide.scalar_power_sound
