import RibbonAllOddCore
import RibbonAffineModCore

namespace RibbonAllOddField
open RibbonAffine (eRow)
variable {K : Type*} [Field K]

def separates (a b : Kˣ) (k : Count) : Prop :=
  ∀ i j : Fin 64, i.val<j.val →
    eRow a b (symbol k i.val)=eRow a b (symbol k j.val) → IsMate (spec k) i.val j.val
instance {p : Nat} [Fact (Nat.Prime p)] (a b : (ZMod p)ˣ) (k : Count) :
    Decidable (separates a b k) := by unfold separates; infer_instance

private theorem transfer (p x y : Nat) [hp : Fact (Nat.Prime p)]
    (a b : Kˣ) (z : (p:K)=0) (A : (a:K)=(x:K)) (B : (b:K)=(y:K))
    (hx : (x:ZMod p)≠0) (hy : (y:ZMod p)≠0) (k : Count)
    (S : separates (Units.mk0 (x:ZMod p) hx) (Units.mk0 (y:ZMod p) hy) k) :
    separates a b k := by
  letI : CharP K p := (CharP.charP_iff_prime_eq_zero (R:=K) hp.out).mpr z
  let f : ZMod p→+*K := ZMod.castHom (dvd_refl p) K
  have X : Units.map f.toMonoidHom (Units.mk0 (x:ZMod p) hx)=a := by
    apply Units.ext
    change f (x:ZMod p)=(a:K)
    rw [map_natCast,A]
  have Y : Units.map f.toMonoidHom (Units.mk0 (y:ZMod p) hy)=b := by
    apply Units.ext
    change f (y:ZMod p)=(b:K)
    rw [map_natCast,B]
  intro i j lt E
  apply S i j lt
  apply RibbonAffine.map_eRow_inj f
  rwa [X,Y]

set_option maxHeartbeats 0
set_option maxRecDepth 20000
local instance prime11 : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance prime13 : Fact (Nat.Prime 13) := ⟨by decide⟩
local instance prime43 : Fact (Nat.Prime 43) := ⟨by decide⟩
def extraCases : Fin 13 → Nat × Nat × Nat × Count := ![(11,3,5,13),(11,3,9,11),(11,4,5,12),(11,4,9,9),(11,5,3,17),(11,5,4,14),(11,9,3,16),(11,9,4,15),(13,3,3,5),(13,3,9,3),(13,9,3,2),(13,9,9,0),(43,31,1,7)]

private theorem extra0 : separates (Units.mk0 ((3:Nat):ZMod 11) (by decide))
    (Units.mk0 ((5:Nat):ZMod 11) (by decide)) 13 := by decide +kernel

private theorem extra1 : separates (Units.mk0 ((3:Nat):ZMod 11) (by decide))
    (Units.mk0 ((9:Nat):ZMod 11) (by decide)) 11 := by decide +kernel

private theorem extra2 : separates (Units.mk0 ((4:Nat):ZMod 11) (by decide))
    (Units.mk0 ((5:Nat):ZMod 11) (by decide)) 12 := by decide +kernel

private theorem extra3 : separates (Units.mk0 ((4:Nat):ZMod 11) (by decide))
    (Units.mk0 ((9:Nat):ZMod 11) (by decide)) 9 := by decide +kernel

private theorem extra4 : separates (Units.mk0 ((5:Nat):ZMod 11) (by decide))
    (Units.mk0 ((3:Nat):ZMod 11) (by decide)) 17 := by decide +kernel

private theorem extra5 : separates (Units.mk0 ((5:Nat):ZMod 11) (by decide))
    (Units.mk0 ((4:Nat):ZMod 11) (by decide)) 14 := by decide +kernel

private theorem extra6 : separates (Units.mk0 ((9:Nat):ZMod 11) (by decide))
    (Units.mk0 ((3:Nat):ZMod 11) (by decide)) 16 := by decide +kernel

private theorem extra7 : separates (Units.mk0 ((9:Nat):ZMod 11) (by decide))
    (Units.mk0 ((4:Nat):ZMod 11) (by decide)) 15 := by decide +kernel

private theorem extra8 : separates (Units.mk0 ((3:Nat):ZMod 13) (by decide))
    (Units.mk0 ((3:Nat):ZMod 13) (by decide)) 5 := by decide +kernel

private theorem extra9 : separates (Units.mk0 ((3:Nat):ZMod 13) (by decide))
    (Units.mk0 ((9:Nat):ZMod 13) (by decide)) 3 := by decide +kernel

private theorem extra10 : separates (Units.mk0 ((9:Nat):ZMod 13) (by decide))
    (Units.mk0 ((3:Nat):ZMod 13) (by decide)) 2 := by decide +kernel

private theorem extra11 : separates (Units.mk0 ((9:Nat):ZMod 13) (by decide))
    (Units.mk0 ((9:Nat):ZMod 13) (by decide)) 0 := by decide +kernel

private theorem extra12 : separates (Units.mk0 ((31:Nat):ZMod 43) (by decide))
    (Units.mk0 ((1:Nat):ZMod 43) (by decide)) 7 := by decide +kernel

theorem extra_separates (a b : Kˣ) (i : Fin 13)
    (P : (((extraCases i).1:Nat):K)=0)
    (A : (a:K)=(((extraCases i).2.1:Nat):K))
    (B : (b:K)=(((extraCases i).2.2.1:Nat):K)) : separates a b (extraCases i).2.2.2 := by
  fin_cases i
  · exact transfer 11 3 5 a b P A B (by decide) (by decide) 13 extra0
  · exact transfer 11 3 9 a b P A B (by decide) (by decide) 11 extra1
  · exact transfer 11 4 5 a b P A B (by decide) (by decide) 12 extra2
  · exact transfer 11 4 9 a b P A B (by decide) (by decide) 9 extra3
  · exact transfer 11 5 3 a b P A B (by decide) (by decide) 17 extra4
  · exact transfer 11 5 4 a b P A B (by decide) (by decide) 14 extra5
  · exact transfer 11 9 3 a b P A B (by decide) (by decide) 16 extra6
  · exact transfer 11 9 4 a b P A B (by decide) (by decide) 15 extra7
  · exact transfer 13 3 3 a b P A B (by decide) (by decide) 5 extra8
  · exact transfer 13 3 9 a b P A B (by decide) (by decide) 3 extra9
  · exact transfer 13 9 3 a b P A B (by decide) (by decide) 2 extra10
  · exact transfer 13 9 9 a b P A B (by decide) (by decide) 0 extra11
  · exact transfer 43 31 1 a b P A B (by decide) (by decide) 7 extra12

end RibbonAllOddField
#print axioms RibbonAllOddField.extra_separates
