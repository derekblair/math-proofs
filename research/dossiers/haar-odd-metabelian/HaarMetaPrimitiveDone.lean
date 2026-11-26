import HaarMetaPrimitiveCore
import HaarMetaS013Haar
import HaarMetaS014Haar
import HaarMetaS025Haar
namespace HaarMetaPrimitiveDone
open HaarMetaEarlyCases
variable {G Q : Type*} [Group G] [CommGroup Q] [Finite G]
variable (odd : Odd (Nat.card G)) (f : G→*Q)
variable (onto : Function.Surjective f) (ab : ∀ a b : f.ker, a*b=b*a)
variable (x y : G) (hx : x≠1) (hy : y≠1) (ne : x≠y) (gen : HaarClass4Generate.Generates x y)
include odd onto ab hx hy ne gen
theorem p013 (h3 : f y=(f x)^3) : Good x y := by
  letI : Fact (∀ a b : f.ker, a*b=b*a) := ⟨ab⟩
  exact HaarMetaPrimitiveCore.p013 odd f onto ab x y hx hy ne gen h3
    (HaarMetaS013Haar.odd_strip f odd x y x (pow_one _).symm h3)
theorem p014 (h4 : f y=(f x)^4) : Good x y := by
  letI : Fact (∀ a b : f.ker, a*b=b*a) := ⟨ab⟩
  exact HaarMetaPrimitiveCore.p014 odd f onto ab x y hx hy ne gen h4
    (HaarMetaS014Haar.odd_strip f odd x y x (pow_one _).symm h4)
theorem p025 (h52 : (f x)^5=(f y)^2) : Good x y := by
  letI : Fact (∀ a b : f.ker, a*b=b*a) := ⟨ab⟩
  exact HaarMetaPrimitiveCore.p025 odd f onto ab x y hx hy ne gen h52
    (HaarMetaS025Haar.odd_strip f odd x y)
end HaarMetaPrimitiveDone
#print axioms HaarMetaPrimitiveDone.p025
