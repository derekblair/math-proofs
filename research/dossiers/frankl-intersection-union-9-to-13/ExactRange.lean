import Exact11
import PackedColor13

namespace IU
set_option maxRecDepth 30000
set_option maxHeartbeats 0

theorem upper13 (F : Sys) (ok : IsIU F 13 2 2) : F.card≤968 :=
  cap_of_prefix ok prefix_cap13

theorem upper12 (F : Sys) (ok : IsIU F 12 2 2) : F.card≤484 :=
  upper_with_free (by decide) F ok upper13

theorem exact12 : Exact 12 484 :=
  ⟨upper12, attained (l:=6) (r:=6) (by decide) (by decide) (by decide) (by decide +kernel)⟩
theorem exact13 : Exact 13 968 :=
  ⟨upper13, attained (l:=6) (r:=6) (by decide) (by decide) (by decide) (by decide +kernel)⟩

theorem intersection_union_9_to_13 :
    Exact 9 50 ∧ Exact 10 110 ∧ Exact 11 220 ∧ Exact 12 484 ∧ Exact 13 968 :=
  ⟨intersection_union_9_2_2,exact10,exact11,exact12,exact13⟩

#print axioms intersection_union_9_to_13
end IU
