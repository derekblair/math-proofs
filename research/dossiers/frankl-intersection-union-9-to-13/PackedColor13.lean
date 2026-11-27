import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
import Color13Slice0
import Color13Slice1
import Color13Slice2
import Color13Slice3
import Color13Slice4
import Color13Slice5
import Color13Slice6
import Color13Slice7
namespace IU
set_option maxRecDepth 16000
set_option maxHeartbeats 0
theorem slices13 (c : Fin 32) : packed (outsideSlice 13 2 2 (256*c.val) 256) = packed (paintSlice pc13.flatten (256*c.val) 256) := by
  fin_cases c
  · exact slice0
  · exact slice1
  · exact slice2
  · exact slice3
  · exact slice4
  · exact slice5
  · exact slice6
  · exact slice7
  · exact slice8
  · exact slice9
  · exact slice10
  · exact slice11
  · exact slice12
  · exact slice13
  · exact slice14
  · exact slice15
  · exact slice16
  · exact slice17
  · exact slice18
  · exact slice19
  · exact slice20
  · exact slice21
  · exact slice22
  · exact slice23
  · exact slice24
  · exact slice25
  · exact slice26
  · exact slice27
  · exact slice28
  · exact slice29
  · exact slice30
  · exact slice31

theorem prefix_cap13 (F : Finset Nat)
    (v : ∀ x∈F, x∈admissible 13 2 2)
    (e : ∀ a∈F, ∀ b∈F, a≠b → edge 13 2 2 a b=true) :
    F.card≤968 := by
  apply clique_cap 13 2 2 pc13 all13_ok F _ e
  intro a aF
  obtain ⟨lt,h⟩ := List.mem_filter.mp (v a aF)
  have lo : a<8192 := List.mem_range.mp lt
  let c : Fin 32 := ⟨a/256,by omega⟩
  apply covered_by_slice (slices13 c) h <;> dsimp [c] <;> omega

#print axioms prefix_cap13

end IU
