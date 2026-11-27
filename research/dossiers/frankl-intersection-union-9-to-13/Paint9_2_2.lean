import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import ColorCore
namespace IU
set_option maxHeartbeats 0
set_option maxRecDepth 20000
def colors9_2_2 : List (List Nat) := [[87], [79], [47], [15], [23], [55], [27], [31], [39], [43], [59, 199], [71, 60], [91, 295], [75, 53], [63, 327], [7, 58], [51, 77], [103, 155], [11, 54], [135, 123], [95, 167], [62, 67], [263, 57], [61, 391], [29, 99], [271, 115], [143, 119], [30, 35], [139, 127], [46, 83], [45, 19], [267, 125], [279, 107], [93, 3], [94, 259], [151, 111], [78, 275], [13, 147, 117], [14, 118, 131], [141, 126, 291], [269, 124, 163], [270, 121, 323], [142, 122, 195], [283, 109], [287, 110, 387], [159], [286], [285], [158], [157]]
theorem cert9_2_2 : proper 9 2 2 colors9_2_2 := by decide +kernel
theorem covered_chunk (c : Fin 8) : ∀ i : Fin 64,
    vertex 9 2 2 (64*c.val+i.val)=true → 64*c.val+i.val ∈ colors9_2_2.flatten := by
  fin_cases c <;> decide +kernel
theorem covered (a : Nat) (h : a ∈ admissible 9 2 2) : a ∈ colors9_2_2.flatten := by
  obtain ⟨H,V⟩ := List.mem_filter.mp h
  have lo : a<512 := List.mem_range.mp H
  let c : Fin 8 := ⟨a/64,by omega⟩
  let i : Fin 64 := ⟨a%64,by omega⟩
  have e : 64*c.val+i.val=a := by dsimp [c,i]; omega
  have C := covered_chunk c i
  rw [e] at C
  exact C V
theorem prefix_clique_9_2_2 (F : Finset Nat)
    (hv : ∀ a ∈ F, a ∈ admissible 9 2 2)
    (edgeF : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → edge 9 2 2 a b = true) :
    F.card ≤ 50 := by
  apply clique_cap 9 2 2 colors9_2_2 cert9_2_2 F _ edgeF
  intro a ha
  exact covered a (hv a ha)
#print axioms prefix_clique_9_2_2
end IU
