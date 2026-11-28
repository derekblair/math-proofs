import N63EnumerationCore
import N63ChartChecker

namespace Erdos151N63

def pairs (q : Nat) : List (Nat × Nat) :=
  (List.range q).flatMap fun u => ((List.range q).filter (u < ·)).map (u, ·)

def graphOfCode (q h : Nat) : Array Nat :=
  let E := ((pairs q).zipIdx.filter fun p => h.testBit p.2).map Prod.fst
  ((List.range q).map fun u => E.foldl (fun r (a,b) =>
    if a=u then r ||| (1 <<< b) else if b=u then r ||| (1 <<< a) else r) 0).toArray

def tfRight (q : Nat) (H : Array Nat) : Bool :=
  (pairs q).all fun (a,b) =>
    !adj H a b || (((mask H a) &&& (mask H b)) == 0)

def allowed (q : Nat) (H : Array Nat) (v : Fin (2^q)) : Bool :=
  (List.range q).all fun j => !v.val.testBit j || (((mask H j) &&& v.val) == 0)

def buildRows (d q : Nat) (H : Array Nat) (f : Fin d → Fin (2^q)) : Array Nat :=
  let ts := (List.finRange d).map fun i => (f i).val
  let l := ts.map fun a => 1 ||| (a <<< (d+1))
  let r := (List.range q).map fun j =>
    ((ts.zipIdx).foldl (fun a (m,i) =>
      if m.testBit j then a ||| (1 <<< (i+1)) else a) 0) |||
      (mask H j <<< (d+1))
  (((1 <<< (d+1))-2)::(l++r)).toArray

def eligibleRows (n m d : Nat) (R : Array Nat) : Bool :=
  let ds := (List.range n).map (deg R n)
  ds.all (fun a => 2 ≤ a && a ≤ d) && decide (2*m ≤ ds.sum)

def enumH (n m d h : Nat) : List (Array Nat) :=
  let q := n-1-d
  let H := graphOfCode q h
  if tfRight q H then
    ((monotoneTuples (2^q) (allowed q H) d 0).map (buildRows d q H)).filter (eligibleRows n m d)
  else []

theorem code_mem_enumH (n m d h : Nat) (f : Fin d → Fin (2^(n-1-d)))
    (mono : ∀ i j : Fin d, i.val ≤ j.val → (f i).val ≤ (f j).val)
    (ha : ∀ i, allowed (n-1-d) (graphOfCode (n-1-d) h) (f i) = true)
    (htf : tfRight (n-1-d) (graphOfCode (n-1-d) h) = true)
    (hdeg : eligibleRows n m d (buildRows d (n-1-d) (graphOfCode (n-1-d) h) f) = true) :
    buildRows d (n-1-d) (graphOfCode (n-1-d) h) f ∈ enumH n m d h := by
  unfold enumH
  simp only [htf,if_true]
  exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨f,mem_monotoneTuples _ _ _ _
    f mono (fun _ => Nat.zero_le _) ha,rfl⟩,hdeg⟩

#print axioms code_mem_enumH
end Erdos151N63
