import BK73Main4
import BK73Assemble4
import BK73LB4Logic
import BK73LB4Chunks
import BK73FinalEq

open SimpleGraph

namespace BK73

/-- Every bridgeless graph of order 7 with at least 11 edges has an orientation of diameter ≤ 4. -/
theorem main4 (G : SimpleGraph (Fin 7)) (hG : Bridgeless G) (hE : 11 ≤ G.edgeSet.ncard) :
    HasOrientDiamLE G 4 := main4_of allL4_top G hG hE

theorem mnd_7_4_le : mnd 7 4 ≤ 11 := Nat.sInf_le (fun G hG hE => main4 G hG hE)

theorem G1_noOrient : ¬ HasOrientDiamLE G1 4 := G1_noOrient_of lb4_top

theorem mnd_7_4_ge : 11 ≤ mnd 7 4 := by
  unfold mnd
  refine le_csInf ⟨11, fun G hG hE => main4 G hG hE⟩ (fun M hM => ?_)
  by_contra hlt
  exact G1_noOrient (hM G1 G1_bridgeless (by rw [G1_ncard]; omega))

/-- m(7,4) = 11, whereas Boriboon–Kittipassorn Conjecture 4 predicts C(3,2)+7+2 = 12. -/
theorem mnd_7_4 : mnd 7 4 = 11 := le_antisymm mnd_7_4_le mnd_7_4_ge

/-- Conjecture 4 also fails at (n,d) = (7,4). -/
theorem conjecture4_false_74 : mnd 7 4 ≠ (7 - 4).choose 2 + 7 + 2 := by
  rw [mnd_7_4]; decide

end BK73

#print axioms BK73.mnd_7_4
#print axioms BK73.conjecture4_false_74
