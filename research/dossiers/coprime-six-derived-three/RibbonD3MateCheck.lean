import RibbonD3MateData

namespace RibbonD3MateData

def erasePorts (side : Bool) (w : List Nat) : List Int :=
  match w with
  | [] => []
  | d :: tail =>
    if d == 2 then erasePorts (!side) tail
    else
      let a : Int := if side then 2 else 1
      (if d == 0 then a else -a) :: erasePorts side tail

def inverse (w : List Int) : List Int := w.reverse.map Neg.neg

def repeatPower (x n : Int) : List Int :=
  List.replicate n.natAbs (if n < 0 then -x else x)

def freeReduce (w : List Int) : List Int :=
  (w.foldl (fun out a =>
    match out with
    | b::bs => if b == -a then bs else a::out
    | [] => [a]) []).reverse

def schreier (keys : Array (Int × Int)) (w : List Int) : Option (List Int) := do
  let (x,y,out) ← (freeReduce w).foldlM (fun (x,y,out) a => do
    if a.natAbs == 1 then pure (x+a,y,out)
    else
      let s : Int := if a > 0 then 1 else -1
      let z := y+s
      if x == 0 then pure (x,z,out)
      else
        let n ← keys.toList.idxOf? (x,min y z)
        pure (x,z,s*((n : Int)+1)::out)
    ) (0,0,[])
  if x == 0 && y == 0 then pure out.reverse else none

def checkR (C : Chart) (r : RRow) : Bool :=
  let pathWord (i : Nat) := erasePorts C.startSide (C.ports.toList.take i)
  let T := pathWord r.j ++ inverse (pathWord r.i)
  let H := repeatPower 1 r.u ++ repeatPower 2 r.v
  let R := pathWord 32
  let Q := H ++ (if r.sign == 1 then R else inverse R) ++ inverse H
  (r.sign == 1 || r.sign == -1) &&
    schreier C.keys T == (C.words[r.leftWord]?).map Array.toList &&
    schreier C.keys Q == (C.words[r.rightWord]?).map Array.toList

def checkRAll : Bool := charts.all fun c => c.rows.all (checkR c)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 12000 in
theorem checkRAll_true : checkRAll = true := by decide +kernel

#print axioms checkRAll_true
end RibbonD3MateData
