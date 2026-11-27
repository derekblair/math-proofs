import Stabilize
import Encode
import Paint9_2_2

namespace IU

theorem upper_bound_9_2_2 (F : Sys) (ok : IsIU F 9 2 2) : F.card≤50 := by
  obtain ⟨H,e,V,s⟩ := stabilize F ok
  have C := prefix_closed_of_elementary H V.1 s
  obtain ⟨c,U,E⟩ := image_in_prefix_graph (by decide : 0<(2:Nat)) V C
  exact (c.trans e) ▸ prefix_clique_9_2_2 _ U E

#print axioms upper_bound_9_2_2
end IU
