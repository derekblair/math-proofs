import N63ArithmeticCode

namespace Erdos151N63

def natTuples (q : Nat) (ok : Nat → Bool) : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | d+1, lo => ((List.range q).filter fun h => lo ≤ h && ok h).flatMap
      fun h => (natTuples q ok d h).map (h :: ·)

theorem mem_natTuples (q : Nat) (ok : Nat → Bool)
    (d : Nat) (lo : Nat) (f : Fin d → Fin q)
    (mono : ∀ i j : Fin d, i.val ≤ j.val → (f i).val ≤ (f j).val)
    (hl : ∀ i, lo ≤ (f i).val) (ha : ∀ i, ok (f i).val = true) :
    (List.finRange d).map (fun i => (f i).val) ∈ natTuples q ok d lo := by
  induction d generalizing lo with
  | zero => simp [natTuples]
  | succ d ih =>
    rw [List.finRange_succ]
    simp only [List.map_cons,List.map_map,natTuples,List.mem_flatMap,List.mem_map]
    refine ⟨(f 0).val,List.mem_filter.mpr ⟨List.mem_range.mpr (f 0).isLt,by simp [hl,ha]⟩,
      (List.finRange d).map (fun i => (f i.succ).val),?_,rfl⟩
    exact ih (f 0).val (fun i => f i.succ)
      (fun i j h => mono _ _ (Nat.succ_le_succ h))
      (fun i => mono _ _ (Nat.zero_le _)) (fun i => ha i.succ)

def allowedMask (q : Nat) (H : Array Nat) (v : Nat) : Bool :=
  (List.range q).all fun j => !v.testBit j || (((mask H j) &&& v) == 0)

def buildRaw (d q : Nat) (H : Array Nat) (ts : List Nat) : Array Nat :=
  let l := ts.map fun a => 1 ||| (a <<< (d+1))
  let r := (List.range q).map fun j =>
    ((ts.zipIdx).foldl (fun a (m,i) =>
      if m.testBit j then a ||| (1 <<< (i+1)) else a) 0) |||
      (mask H j <<< (d+1))
  (((1 <<< (d+1))-2)::(l++r)).toArray

def pop (q m : Nat) : Nat := ((List.range q).filter m.testBit).length

def rawDegrees (d q : Nat) (H : Array Nat) (ts : List Nat) : List Nat :=
  d :: (ts.map fun m => 1+pop q m) ++ ((List.range q).map fun j =>
    pop q (mask H j) + (ts.filter (·.testBit j)).length)

def rawDegreeOK (n m d q : Nat) (H : Array Nat) (ts : List Nat) : Bool :=
  let ds := rawDegrees d q H ts
  ds.length == n && ds.all (fun a => 2 ≤ a && a ≤ d) && decide (2*m ≤ ds.sum)

def enumFast (n m d h : Nat) : List (Array Nat) :=
  let q := n-1-d
  let H := graphOfCode q h
  if tfRight q H then
    ((natTuples (2^q) (allowedMask q H) d 0).filter (rawDegreeOK n m d q H)).map (buildRaw d q H)
  else []

theorem code_mem_enumFast (n m d h : Nat) (f : Fin d → Fin (2^(n-1-d)))
    (mono : ∀ i j : Fin d, i.val ≤ j.val → (f i).val ≤ (f j).val)
    (ha : ∀ i, allowed (n-1-d) (graphOfCode (n-1-d) h) (f i) = true)
    (htf : tfRight (n-1-d) (graphOfCode (n-1-d) h) = true)
    (hdeg : rawDegreeOK n m d (n-1-d) (graphOfCode (n-1-d) h)
      ((List.finRange d).map (fun i => (f i).val)) = true) :
    buildRows d (n-1-d) (graphOfCode (n-1-d) h) f ∈ enumFast n m d h := by
  unfold enumFast
  simp only [htf,if_true]
  apply List.mem_map.mpr
  refine ⟨_, List.mem_filter.mpr ⟨?_,hdeg⟩,rfl⟩
  exact mem_natTuples _ _ d 0 f mono (fun _ => Nat.zero_le _) ha

#print axioms code_mem_enumFast
end Erdos151N63
