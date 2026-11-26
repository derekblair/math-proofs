import RibbonOrderThreeUse
import RibbonOddInterfaces

namespace RibbonOddFinite
open RibbonOrderThree RibbonOdd

def inputLabel (i : Fin 28) : Triple :=
  ((inputs i).p,(inputs i).a,(inputs i).b)
def Bad (v : Triple) : Prop := ∃ i : Fin 28, v=inputLabel i

theorem digit_one : ∀ i : Fin 28, digit (inputs i).p (inputs i).a=1 ↔ (inputs i).a=1 := by decide +kernel

end RibbonOddFinite
