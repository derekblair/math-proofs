import BK73Main1
import BK73Assemble

open SimpleGraph

namespace BK73

/-- Every bridgeless graph of order 7 with at least 14 edges has an orientation of diameter ≤ 3. -/
theorem main (G : SimpleGraph (Fin 7)) (hG : Bridgeless G) (hE : 14 ≤ G.edgeSet.ncard) :
    HasOrientDiamLE G 3 := main_of allL_top G hG hE

theorem mnd_7_3_le : mnd 7 3 ≤ 14 := Nat.sInf_le (fun G hG hE => main G hG hE)

/-- Boriboon–Kittipassorn (arXiv:2508.17569) Conjecture 4 fails at (n,d) = (7,3):
the conjectured value is C(4,2)+7+2 = 15 but m(7,3) ≤ 14. -/
theorem conjecture4_false :
    ¬ (∀ n d : ℕ, 2 ≤ d → d ≤ n - 2 → mnd n d = (n - d).choose 2 + n + 2) := by
  intro h
  have h1 := h 7 3 (by decide) (by decide)
  have h2 := mnd_7_3_le
  rw [h1] at h2
  revert h2; decide

end BK73

#print axioms BK73.mnd_7_3_le
#print axioms BK73.conjecture4_false
