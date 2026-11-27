import HaarMetaFirstTorsionCore
import HaarMetaTorsionOneHaar
namespace HaarMetaFirstTorsion
open HaarMetaEarlyCases
variable {G Q : Type*} [Group G] [CommGroup Q] [Finite G] [Finite Q]
theorem first (odd : Odd (Nat.card G)) (f : G→*Q)
    (onto : Function.Surjective f) (ab : ∀ a b : f.ker, a*b=b*a)
    (x y : G) (hx : x≠1) (hy : y≠1) (ne : x≠y) (gen : HaarClass4Generate.Generates x y)
    (h3 : (f x)^3=1) : Good x y := by
  letI : Fact (∀ a b : f.ker, a*b=b*a) := ⟨ab⟩
  exact HaarMetaFirstTorsionCore.first odd f onto ab x y hx hy ne gen h3
    (HaarMetaTorsionOneHaar.odd_cylinder f odd x y y x rfl rfl h3)
end HaarMetaFirstTorsion
#print axioms HaarMetaFirstTorsion.first
