import RibbonD3LowValues
import RibbonD3ChartCycles

namespace RibbonD3Low
open RibbonD3WordSelection Ribbon5Bridge RibbonD3PortEval

def pChart (b : Bool) : Count := if b then 9 else 7
def tabLow (b : Bool) : Array Q := if b then lowValues7 else lowValues5

theorem numericStep : ∀ (b : Bool) (n : Fin 128),
    push (tabLow b)[n.val]! (block (pChart b) 128)[n.val]! =
      (tabLow b)[n.val+1]! := by decide +kernel

theorem initial (b : Bool) :
    (tabLow b)[0]! = (false,0,0,0) := by cases b <;> decide +kernel

end RibbonD3Low
