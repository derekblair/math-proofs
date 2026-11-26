import BK73Graph2
import BK73Core4

open SimpleGraph

namespace BK73

section reach4
variable (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj] (t : ℕ)

theorem good4_sound (hg : good4 (ofBits (codeList G)) t = true) (u v : Fin 7) :
    ∃ k ≤ 4, DReach (arcT G t) k u v := by
  rw [good4, goodOs4, List.all_eq_true] at hg
  have h := hg u (List.mem_range.mpr u.isLt)
  rw [beq_iff_eq, reach4] at h
  have hI := inv_step G t u 3 _ (inv_step G t u 2 _
    (inv_step G t u 1 _ (inv_step G t u 0 _ (inv_zero G t u))))
  have hb : (step ((List.range 7).map (orow (ofBits (codeList G)) t))
      (step ((List.range 7).map (orow (ofBits (codeList G)) t))
      (step ((List.range 7).map (orow (ofBits (codeList G)) t))
        (step ((List.range 7).map (orow (ofBits (codeList G)) t)) (2 ^ (u:ℕ)))))).testBit v
      = true := by
    rw [h, show (127:ℕ) = 2^7 - 1 from rfl, Nat.testBit_two_pow_sub_one]; simpa using v.isLt
  obtain ⟨_, j, hj, hr⟩ := hI v hb
  exact ⟨j, hj, hr⟩

theorem good4_hasOrient (hg : good4 (ofBits (codeList G)) t = true) : HasOrientDiamLE G 4 :=
  ⟨orientT G t, good4_sound G t hg⟩

end reach4

end BK73
