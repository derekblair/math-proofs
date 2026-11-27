import FastColor

namespace IU
def outsideSlice (n p q start width : Nat) : List Nat :=
  (List.range width).filter (fun i => vertex n p q (start+i))

def paintSlice (L : List Nat) (start width : Nat) : List Nat :=
  (L.filter (fun a => decide (start≤a ∧ a<start+width))).map (·-start)

theorem covered_by_slice {n p q base width a : Nat} {L : List Nat}
    (cert : packed (outsideSlice n p q base width) = packed (paintSlice L base width))
    (hv : vertex n p q a=true) (lower : base≤a) (upper : a<base+width) : a∈L := by
  have M : a-base ∈ outsideSlice n p q base width := by
    apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr (by omega),by rwa [Nat.add_sub_of_le lower]⟩
  have bit := (packed_mem _ _).mpr M
  rw [cert] at bit
  obtain ⟨z,hz,e⟩ := List.mem_map.mp ((packed_mem _ _).mp bit)
  obtain ⟨zL,zi⟩ := List.mem_filter.mp hz
  have zlo := (of_decide_eq_true zi).1
  have U : z=a := by omega
  exact U ▸ zL

theorem proper_flatten {n p q : Nat} {L : List (List (List Nat))}
    (h : ∀ C∈L, proper n p q C) : proper n p q L.flatten := by
  intro cls mem
  obtain ⟨C,H,Cc⟩ := List.mem_flatten.mp mem
  exact h C H cls Cc

end IU
