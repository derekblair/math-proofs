import RibbonD3MateCheckAPI

namespace RibbonD3MateData

def opposite (d : Nat) := if d == 0 then 1 else if d == 1 then 0 else 2
def reversePorts (w : List Nat) := w.reverse.map opposite

def axisExponent (d : Int) (w : List Int) : Int :=
  (w.count d : Int) - (w.count (-d) : Int)

def isBalanced (b : Bool) (w : List Nat) : Bool :=
  let L := erasePorts b w
  w.count 2 % 2 == 0 && axisExponent 1 L == 0 && axisExponent 2 L == 0

def checkClosure (C : Chart) : Bool :=
  let A := C.ports.toList.take 32
  let W := C.ports.toList.take 64
  let U := A.take C.rotation
  C.ports.size == 128 &&
  C.ports.all (· ≤ 2) &&
  C.rotation < 32 &&
  isBalanced C.startSide U &&
  W == A ++ reversePorts (A.drop C.rotation ++ U) &&
  C.ports.toList == W ++ reversePorts (W.drop C.rotation ++ U) &&
  isBalanced C.startSide A &&
  match schreier C.keys (erasePorts C.startSide A) with
  | none => false
  | some L =>
    (List.range C.keys.size).all (fun k => axisExponent ((k : Int)+1) L == 0)

def checkClosureAll : Bool := charts.all checkClosure

set_option maxHeartbeats 600000 in
set_option maxRecDepth 5000 in
theorem checkClosureAll_true : checkClosureAll = true := by decide +kernel

theorem checkClosure_true (i : Fin charts.size) : checkClosure charts[i] = true :=
  Array.all_eq_true.mp checkClosureAll_true i.val i.isLt

#print axioms checkClosureAll_true
end RibbonD3MateData
