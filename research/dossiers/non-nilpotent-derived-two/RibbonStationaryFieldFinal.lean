import RibbonStationaryFieldFinalCore
import RibbonStationarySlopeFinal

namespace RibbonStationaryField
open RibbonStationaryWord
variable {K : Type*} [Field K]

theorem field_words (a b : Kˣ) (n : Nat) (two : (2:K)≠0) (odd : Odd n) (no3 : ¬3∣n)
    (aN : a^n=1) (bN : b^n=1) (a1 : a≠1) :
    (∃ k : Count, separates a b k) ∨ FieldResidual a b :=
  field_words_of slope_full a b n two odd no3 aN bN a1

end RibbonStationaryField
#print axioms RibbonStationaryField.field_words
