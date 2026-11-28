import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

namespace Erdos151N62

/-- The support of an eligible retained vertex avoids every edge of the P4. -/
def P4Independent (S : Finset (Fin 4)) : Prop :=
  ∀ i j : Fin 4, i ∈ S → j ∈ S → i.val+1 ≠ j.val

instance (S : Finset (Fin 4)) : Decidable (P4Independent S) := by
  unfold P4Independent
  infer_instance

/-- P4 supports are 3-Helly on pairwise intersections: a conflict triangle
would necessarily occur inside one original hub's neighborhood. -/
theorem p4_local_helly :
    ∀ A B C : Finset (Fin 4), P4Independent A → P4Independent B → P4Independent C →
      (A∩B).Nonempty → (A∩C).Nonempty → (B∩C).Nonempty → (A∩B∩C).Nonempty := by
  decide +kernel

/-- The lower bounds on both projection degrees bound the total number
of ambient nonlone edges at a retained vertex. The directed partition
of residual incidences is shared lone plus red-only plus blue-only. -/
theorem core_incidences_from_two_projections
    (ambient residual core lone red blue lower : Nat)
    (part : residual=lone+red+blue)
    (hred : lower≤lone+red) (hblue : lower≤lone+blue)
    (cap : core ≤ ambient-residual+red+blue) (sub : residual≤ambient) :
    core+2*lower ≤ ambient+residual := by omega

theorem pool35_no_lost_core (ambient residual core lone red blue : Nat)
    (part : residual=lone+red+blue)
    (hred : 8≤lone+red) (hblue : 8≤lone+blue)
    (cap : core ≤ ambient-residual+red+blue)
    (ha : ambient≤12) (hr : residual≤ambient) (hc : 8≤core) :
    residual=ambient ∧ ambient=12 := by
  have := core_incidences_from_two_projections _ _ _ _ _ _ 8 part hred hblue cap hr
  omega

theorem pool34_five_lost_excludes (ambient residual core lone red blue : Nat)
    (part : residual=lone+red+blue)
    (hred : 6≤lone+red) (hblue : 6≤lone+blue)
    (cap : core ≤ ambient-residual+red+blue)
    (ha : ambient≤12) (hr : residual+5≤ambient) (hc : 8≤core) : False := by
  have := core_incidences_from_two_projections _ _ _ _ _ _ 6 part hred hblue cap (by omega)
  omega

#print axioms p4_local_helly
#print axioms pool35_no_lost_core
#print axioms pool34_five_lost_excludes
end Erdos151N62
