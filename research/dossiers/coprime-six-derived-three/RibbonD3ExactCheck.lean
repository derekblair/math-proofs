import RibbonD3MateCheck
import RibbonD3ExactData

namespace RibbonD3MateData
def checkExact (C : Chart) (p : ExactRow) : Bool :=
  let w (i : Nat) := erasePorts C.startSide (C.ports.toList.take i)
  let A := w p.baseLength
  let T := w p.j ++ inverse (w p.i)
  let V := p.conjugator ++ (if p.sign == 1 then A else inverse A) ++ inverse p.conjugator
  (p.baseLength == 32 || p.baseLength == 64) &&
  (p.sign == 1 || p.sign == -1) &&
  (p.baseLength ≤ p.j) &&
  (if p.baseLength == 32 then p.j < 64 else p.j-p.i == 64) &&
  freeReduce T == freeReduce V

def checkExactAll : Bool :=
  (List.range charts.size).all (fun k => (exactRows[k]!).all (checkExact charts[k]!))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 12000 in
theorem checkExactAll_true : checkExactAll = true := by decide +kernel

#print axioms checkExactAll_true
end RibbonD3MateData
