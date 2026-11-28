import AtlasPack

namespace BikovEight

def colors : Array Nat := #[42240000, 42240000, 42239104, 4984896, 8651904, 2363520, 8651904]
def color (i : Fin 7) (a b : Fin 8) : Bool := colors[i.val]!.testBit (edgeID a.val b.val)

def obstruction (i : Fin 7) (s : Nat) : Bool :=
  orderedEdges.any fun (a,b) =>
    hasEdge names[i.val]! a b &&
    (s.testBit a == colors[i.val]!.testBit (edgeID a b)) &&
    (s.testBit b == colors[i.val]!.testBit (edgeID a b))

set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem obstructs (i : Fin 7) (s : Nat) (hs : s<256) : obstruction i s=true := by
  have h : ∀ k : Fin 7, ∀ n ∈ List.range 256, obstruction k n=true := by decide +kernel
  exact h i s (List.mem_range.mpr hs)

/-- Each of the seven named models really is marked, not only necessary. -/
theorem each_name_marked (i : Fin 7) :
    (∀ a b, color i a b=color i b a) ∧
    ∀ f : Fin 8→Bool, ∃ a b, Erdos151MarkedLinkTable.adj i a b=true ∧
      f a=color i a b ∧ f b=color i a b := by
  refine ⟨fun a b=>by simp [color,edgeID,min_comm,max_comm],?_⟩
  intro f
  let g (j : Nat) := f (Fin.ofNat 8 j)
  let s := packF g 8
  have H := obstructs i s (packF_small g 8)
  unfold obstruction at H
  obtain ⟨⟨a,b⟩,mem,h⟩ := List.any_eq_true.mp H
  obtain ⟨alt,b8⟩ := (ordered_iff a b).mp mem
  have a8 : a<8 := lt_trans alt b8
  have eqA : (Fin.ofNat 8 a).val=a := Nat.mod_eq_of_lt a8
  have eqB : (Fin.ofNat 8 b).val=b := Nat.mod_eq_of_lt b8
  have hh : hasEdge names[i.val]! a b=true ∧
      s.testBit a=colors[i.val]!.testBit (edgeID a b) ∧
      s.testBit b=colors[i.val]!.testBit (edgeID a b) := by simpa [Bool.and_eq_true,and_assoc] using h
  refine ⟨Fin.ofNat 8 a,Fin.ofNat 8 b,?_,?_,?_⟩
  · rw [←packed_names,eqA,eqB]
    exact hh.1
  · rw [show f (Fin.ofNat 8 a)=s.testBit a from (packF_bit g a 8 a8).symm]
    unfold color
    rw [eqA,eqB]
    exact hh.2.1
  · rw [show f (Fin.ofNat 8 b)=s.testBit b from (packF_bit g b 8 b8).symm]
    unfold color
    rw [eqA,eqB]
    exact hh.2.2

#print axioms each_name_marked
end BikovEight
