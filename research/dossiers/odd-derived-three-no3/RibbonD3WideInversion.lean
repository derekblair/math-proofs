import RibbonD3WideInversionCore
import RibbonD3WideSlope

namespace RibbonD3Wide
variable {K : Type*} [Field K]

theorem inversion_cover (a b : Kˣ) (n : Nat)
    (odd : Odd n) (two : (2:K)≠0) (three : (3:K)≠0)
    (an : a^n=1) (bn : b^n=1) (a1 : a≠1) :
    InvertedSeparates a b ∨ FieldBad a b :=
  inversion_cover_of_slopes slope_cases a b n odd two three an bn a1

end RibbonD3Wide
#print axioms RibbonD3Wide.inversion_cover
