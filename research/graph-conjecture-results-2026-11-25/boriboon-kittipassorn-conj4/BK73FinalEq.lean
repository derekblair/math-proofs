import BK73Final
import BK73LBLogic
import BK73LBChunks

open SimpleGraph

namespace BK73

theorem G0_noOrient : ¬ HasOrientDiamLE G0 3 := G0_noOrient_of lb_top

/-- the lower bound: FCZnw is bridgeless with 13 edges and no orientation of diameter ≤ 3 -/
theorem mnd_7_3_ge : 14 ≤ mnd 7 3 := by
  unfold mnd
  refine le_csInf ⟨14, fun G hG hE => main G hG hE⟩ (fun M hM => ?_)
  by_contra hlt
  exact G0_noOrient (hM G0 G0_bridgeless (by rw [G0_ncard]; omega))

/-- m(7,3) = 14, whereas Boriboon–Kittipassorn Conjecture 4 predicts 15. -/
theorem mnd_7_3 : mnd 7 3 = 14 := le_antisymm mnd_7_3_le mnd_7_3_ge

end BK73

#print axioms BK73.G0_noOrient
#print axioms BK73.mnd_7_3
